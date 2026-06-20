import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { spawn, spawnSync, type ChildProcess } from "node:child_process";
import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createServer } from "node:net";
import { homedir } from "node:os";
import { dirname, join } from "node:path";
import {
  buildManagedProxyConfig,
  managedProviderFor,
  preferredPortFor,
  providerIds,
  registerManagedProviders,
  type ManagedProvider,
  type ManagedProxyConfig,
  type ProviderModel,
} from "./provider-registry.ts";

type StatusLevel =
  | "idle"
  | "starting"
  | "running"
  | "external"
  | "failed"
  | "stopped";
type ShutdownMode = "sticky" | "session";
type UiLevel = "info" | "warn" | "error" | "success";
type PortDisposition = "headroom" | "free" | "occupied";

type ExtensionCtx = {
  model?: ProviderModel;
  ui: {
    notify(message: string, level?: UiLevel): void;
    setStatus?: (id: string, text: string) => void;
  };
};

type ModelSelectEvent = { model?: ProviderModel };
type SessionShutdownEvent = { reason?: string };

interface ManagedProxyState {
  provider: ManagedProvider;
  port: number;
  rootUrl: string;
  routedBaseUrl: string;
  owned: boolean;
  pid?: number;
  process?: ChildProcess;
  status: StatusLevel;
  lastHealthyAt?: number;
  lastError?: string;
}

interface RouteMetadata {
  provider: ManagedProvider;
  port: number;
  rootUrl: string;
  routedBaseUrl: string;
  version: number;
}

interface OwnerMetadata {
  provider: ManagedProvider;
  pid: number;
  port: number;
  startedAt: string;
  version: number;
}

interface PortAssessment {
  disposition: PortDisposition;
  config: ManagedProxyConfig;
}

interface PerfSummary {
  requestCount: number;
  tokensSaved: number;
  savingsUsd?: number;
  savingsPercent: number;
  basis: "history" | "runtime";
}

interface SupervisorState {
  proxies: Map<ManagedProvider, ManagedProxyState>;
  pending: Map<ManagedProvider, Promise<ManagedProxyState>>;
  perf: Map<ManagedProvider, PerfSummary>;
  cleanupInstalled: boolean;
  cleaningUp: boolean;
  installWarningShown: boolean;
}

const METADATA_VERSION = 1;
const STATUS_SLOT = "pi-headroom";
const DEFAULT_HOST = process.env.PI_HEADROOM_HOST?.trim() || "127.0.0.1";
const HEADROOM_BIN = process.env.PI_HEADROOM_BIN?.trim() || "headroom";
const STATUS_COMMAND =
  process.env.PI_HEADROOM_STATUS_COMMAND?.trim() || "headroom-status";
const STOP_COMMAND =
  process.env.PI_HEADROOM_STOP_COMMAND?.trim() || "headroom-stop";
const RESTART_COMMAND =
  process.env.PI_HEADROOM_RESTART_COMMAND?.trim() || "headroom-restart";
const VERBOSE = isEnabled(process.env.PI_HEADROOM_VERBOSE);
const AUTOSTART = isDefaultEnabled(process.env.PI_HEADROOM_AUTOSTART, true);
const SHUTDOWN_MODE = parseShutdownMode(process.env.PI_HEADROOM_SHUTDOWN_MODE);
const PROBE_TIMEOUT_MS = parsePositiveInt(
  process.env.PI_HEADROOM_PROBE_TIMEOUT_MS,
  1500,
);
const START_TIMEOUT_MS = parsePositiveInt(
  process.env.PI_HEADROOM_START_TIMEOUT_MS,
  30000,
);
const PROBE_INTERVAL_MS = parsePositiveInt(
  process.env.PI_HEADROOM_PROBE_INTERVAL_MS,
  500,
);
const HEALTH_TTL_MS = parsePositiveInt(
  process.env.PI_HEADROOM_HEALTH_TTL_MS,
  5000,
);
const PORT_SCAN_LIMIT = parsePositiveInt(
  process.env.PI_HEADROOM_PORT_SCAN_LIMIT,
  20,
);
const STATE_DIR =
  process.env.PI_HEADROOM_STATE_DIR?.trim() ||
  join(homedir(), ".headroom", "pi-supervisor");

let resolvedConfigs: Record<ManagedProvider, ManagedProxyConfig> | undefined;
let initPromise:
  | Promise<Record<ManagedProvider, ManagedProxyConfig>>
  | undefined;
let headroomInstallProblem: string | undefined;

function isEnabled(raw: string | undefined): boolean {
  return /^(1|true|yes|on)$/i.test(raw ?? "");
}

function isDefaultEnabled(raw: string | undefined, fallback: boolean): boolean {
  if (!raw?.trim()) return fallback;
  return isEnabled(raw);
}

function parsePositiveInt(raw: string | undefined, fallback: number): number {
  if (!raw?.trim()) return fallback;
  const value = Number.parseInt(raw.trim(), 10);
  return Number.isFinite(value) && value > 0 ? value : fallback;
}

function parseShutdownMode(raw: string | undefined): ShutdownMode {
  return raw?.trim().toLowerCase() === "session" ? "session" : "sticky";
}

function routeMetadataPath(provider: ManagedProvider): string {
  return join(STATE_DIR, "routes", `${provider}.json`);
}

function ownerMetadataPath(provider: ManagedProvider): string {
  return join(STATE_DIR, "owners", `${provider}.json`);
}

function globalState(): SupervisorState {
  const g = globalThis as typeof globalThis & {
    __piHeadroomSupervisor__?: Partial<SupervisorState>;
  };
  if (!g.__piHeadroomSupervisor__) {
    g.__piHeadroomSupervisor__ = {};
  }

  const state = g.__piHeadroomSupervisor__;
  if (!(state.proxies instanceof Map)) state.proxies = new Map();
  if (!(state.pending instanceof Map)) state.pending = new Map();
  if (!(state.perf instanceof Map)) state.perf = new Map();
  if (typeof state.cleanupInstalled !== "boolean")
    state.cleanupInstalled = false;
  if (typeof state.cleaningUp !== "boolean") state.cleaningUp = false;
  if (typeof state.installWarningShown !== "boolean")
    state.installWarningShown = false;

  return state as SupervisorState;
}

function processAlive(pid: number | undefined): boolean {
  if (!pid || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

function buildBaseState(
  config: ManagedProxyConfig,
  owned: boolean,
): ManagedProxyState {
  return {
    provider: config.provider,
    port: config.port,
    rootUrl: config.rootUrl,
    routedBaseUrl: config.routedBaseUrl,
    owned,
    status: owned ? "stopped" : "external",
  };
}

function readJsonFile<T>(path: string): T | undefined {
  try {
    return JSON.parse(readFileSync(path, "utf8")) as T;
  } catch {
    return undefined;
  }
}

function loadRoute(provider: ManagedProvider): RouteMetadata | undefined {
  const raw = readJsonFile<Partial<RouteMetadata>>(routeMetadataPath(provider));
  if (
    !raw ||
    raw.provider !== provider ||
    typeof raw.port !== "number" ||
    typeof raw.rootUrl !== "string" ||
    typeof raw.routedBaseUrl !== "string"
  ) {
    return undefined;
  }
  return {
    provider,
    port: raw.port,
    rootUrl: raw.rootUrl,
    routedBaseUrl: raw.routedBaseUrl,
    version: typeof raw.version === "number" ? raw.version : METADATA_VERSION,
  };
}

function saveRoute(config: ManagedProxyConfig): void {
  const path = routeMetadataPath(config.provider);
  mkdirSync(dirname(path), { recursive: true });
  const payload: RouteMetadata = {
    provider: config.provider,
    port: config.port,
    rootUrl: config.rootUrl,
    routedBaseUrl: config.routedBaseUrl,
    version: METADATA_VERSION,
  };
  writeFileSync(path, JSON.stringify(payload, null, 2));
}

function loadOwner(provider: ManagedProvider): OwnerMetadata | undefined {
  const raw = readJsonFile<Partial<OwnerMetadata>>(ownerMetadataPath(provider));
  if (
    !raw ||
    raw.provider !== provider ||
    typeof raw.pid !== "number" ||
    typeof raw.port !== "number"
  ) {
    return undefined;
  }
  return {
    provider,
    pid: raw.pid,
    port: raw.port,
    startedAt:
      typeof raw.startedAt === "string"
        ? raw.startedAt
        : new Date().toISOString(),
    version: typeof raw.version === "number" ? raw.version : METADATA_VERSION,
  };
}

function saveOwner(config: ManagedProxyConfig, proxy: ManagedProxyState): void {
  if (!proxy.pid) return;
  const path = ownerMetadataPath(config.provider);
  mkdirSync(dirname(path), { recursive: true });
  const payload: OwnerMetadata = {
    provider: config.provider,
    pid: proxy.pid,
    port: config.port,
    startedAt: new Date().toISOString(),
    version: METADATA_VERSION,
  };
  writeFileSync(path, JSON.stringify(payload, null, 2));
}

function clearOwner(provider: ManagedProvider): void {
  rmSync(ownerMetadataPath(provider), { force: true });
}

function getConfig(provider: ManagedProvider): ManagedProxyConfig {
  if (!resolvedConfigs) {
    throw new Error("Headroom provider supervisor is not initialized yet.");
  }
  return resolvedConfigs[provider];
}

function dashboardUrl(config: ManagedProxyConfig): string {
  return `${config.rootUrl}/dashboard`;
}

function formatCompactMetric(value: number): string {
  const abs = Math.abs(value);
  if (abs >= 1_000_000_000) return `${(value / 1_000_000_000).toFixed(1)}B`;
  if (abs >= 1_000_000) return `${(value / 1_000_000).toFixed(1)}M`;
  if (abs >= 1_000) return `${(value / 1_000).toFixed(1)}k`;
  return String(Math.round(value));
}

function formatSavingsPercent(value: number): string {
  return `${Math.round(value)}%`;
}

function formatCompactUsd(value: number): string {
  const abs = Math.abs(value);
  if (abs >= 1_000_000_000) return `$${(value / 1_000_000_000).toFixed(1)}B`;
  if (abs >= 1_000_000) return `$${(value / 1_000_000).toFixed(1)}M`;
  if (abs >= 1_000) return `$${(value / 1_000).toFixed(1)}k`;
  return `$${value.toFixed(1)}`;
}

function deriveSavingsPercent(
  tokensSaved: number,
  totalInputTokens: number,
): number {
  const totalBefore = Math.max(0, totalInputTokens) + Math.max(0, tokensSaved);
  return totalBefore > 0 ? (tokensSaved / totalBefore) * 100 : 0;
}

function parsePerfSummary(payload: unknown): PerfSummary | undefined {
  if (!payload || typeof payload !== "object") return undefined;
  const data = payload as {
    lifetime?: {
      requests?: number;
      tokens_saved?: number;
      compression_savings_usd?: number;
      total_input_tokens?: number;
    };
    persistent_savings?: {
      lifetime?: {
        requests?: number;
        tokens_saved?: number;
        compression_savings_usd?: number;
        total_input_tokens?: number;
      };
    };
    requests?: { total?: number };
    tokens?: { saved?: number; savings_percent?: number };
  };

  const lifetime = data.lifetime ?? data.persistent_savings?.lifetime;
  if (
    typeof lifetime?.requests === "number" &&
    typeof lifetime?.tokens_saved === "number"
  ) {
    return {
      requestCount: lifetime.requests,
      tokensSaved: lifetime.tokens_saved,
      savingsUsd:
        typeof lifetime.compression_savings_usd === "number"
          ? lifetime.compression_savings_usd
          : undefined,
      savingsPercent: deriveSavingsPercent(
        lifetime.tokens_saved,
        lifetime.total_input_tokens ?? 0,
      ),
      basis: "history",
    };
  }

  const requestCount = data.requests?.total;
  const tokensSaved = data.tokens?.saved;
  const savingsPercent = data.tokens?.savings_percent;
  if (typeof requestCount !== "number") return undefined;
  if (typeof tokensSaved !== "number") return undefined;
  if (typeof savingsPercent !== "number") return undefined;
  return { requestCount, tokensSaved, savingsPercent, basis: "runtime" };
}

async function refreshPerfSummary(
  provider: ManagedProvider,
  options: { fresh?: boolean } = {},
): Promise<void> {
  if (headroomInstallProblem) return;
  const config = getConfig(provider);
  if (!(await probeLiveness(config.rootUrl))) return;

  const urls = options.fresh
    ? [`${config.rootUrl}/stats-history`, `${config.rootUrl}/stats`]
    : [`${config.rootUrl}/stats?cached=1`, `${config.rootUrl}/stats-history`];

  for (const url of urls) {
    try {
      const response = await fetch(url);
      if (!response.ok) continue;
      const payload = (await response.json()) as unknown;
      const summary = parsePerfSummary(payload);
      if (!summary) continue;
      globalState().perf.set(provider, summary);
      return;
    } catch {
      // best-effort UI metric refresh only
    }
  }
}

function activeStatusLine(model: ProviderModel | undefined): string {
  const provider = managedProviderFor(model);
  if (!provider) return "Headroom: off";
  if (headroomInstallProblem)
    return `Headroom:${provider} unavailable | pi defaults`;

  const config = getConfig(provider);
  const proxy = globalState().proxies.get(provider);
  const perf = globalState().perf.get(provider);
  const status = proxy?.status ?? "idle";
  const owner = proxy?.owned ? "own" : proxy ? "ext" : "?";
  const fallback =
    config.port === config.preferredPort
      ? ""
      : ` fallback-from-${config.preferredPort}`;
  const perfScope = perf?.basis === "history" ? "hist " : "";
  const usdSuffix =
    typeof perf?.savingsUsd === "number"
      ? ` | ${formatCompactUsd(perf.savingsUsd)}`
      : "";
  const perfSuffix = perf
    ? ` | ${perfScope}saved ${formatCompactMetric(perf.tokensSaved)}${usdSuffix} | ${formatSavingsPercent(perf.savingsPercent)}`
    : "";

  if (status === "failed") return `Headroom:${provider} failed${fallback}`;
  if (status === "starting") return `Headroom:${provider} starting${fallback}`;
  if (status === "running" || status === "external") {
    return `Headroom:${provider} ${status}/${owner}${fallback}${perfSuffix}`;
  }
  return `Headroom:${provider} ${status}${fallback}${perfSuffix}`;
}

function updateUiStatus(
  ctx: ExtensionCtx,
  model: ProviderModel | undefined = ctx.model,
): void {
  ctx.ui.setStatus?.(STATUS_SLOT, activeStatusLine(model));
}

function statusLines(model: ProviderModel | undefined): string[] {
  const activeProvider = managedProviderFor(model);
  const state = globalState();
  const activeProxyLines = providerIds().flatMap((provider) => {
    const config = getConfig(provider);
    const proxy = state.proxies.get(provider);
    const status = proxy?.status ?? "idle";
    if (status === "idle" || status === "stopped") return [];
    const ownership = proxy?.owned
      ? `owned pid=${proxy.pid ?? "?"}`
      : proxy
        ? "external"
        : "unknown";
    const error = proxy?.lastError ? ` error=${proxy.lastError}` : "";
    const fallback =
      config.port === config.preferredPort
        ? ""
        : ` fallback-from=${config.preferredPort}`;
    return [
      `- ${provider}: ${config.routedBaseUrl} [${status}; ${ownership}]${fallback}${error}`,
      `  dashboard: ${dashboardUrl(config)}`,
    ];
  });
  const activeCount = providerIds().filter((provider) => {
    const status = state.proxies.get(provider)?.status ?? "idle";
    return status !== "idle" && status !== "stopped";
  }).length;

  return [
    `Managed provider: ${activeProvider ?? "(current model is unmanaged)"}`,
    `Current model: ${model ? `${model.provider}/${model.id ?? "(unknown)"}` : "(none)"}`,
    `Current model base URL: ${model?.baseUrl ?? "(none)"}`,
    `Active dashboard: ${activeProvider ? dashboardUrl(getConfig(activeProvider)) : "(none)"}`,
    `Footer status: ${activeStatusLine(model)}`,
    `Headroom CLI: ${headroomInstallProblem ?? "available"}`,
    `Autostart: ${AUTOSTART ? "enabled" : "disabled"}`,
    `Shutdown mode: ${SHUTDOWN_MODE}`,
    `Port scan limit: ${PORT_SCAN_LIMIT}`,
    `Managed proxies: ${activeCount} active / ${providerIds().length} configured`,
    "Unmanaged providers fall back to pi defaults.",
    "Proxy map:",
    ...(activeProxyLines.length
      ? activeProxyLines
      : ["(no active managed proxies)"]),
  ];
}

function detectPlatformInstallHint(): string {
  switch (process.platform) {
    case "darwin":
      return 'Install Headroom first, then reload pi. Example: curl -fsSL https://raw.githubusercontent.com/chopratejas/headroom/main/scripts/install.sh | "$(brew --prefix bash)/bin/bash"';
    case "linux":
      return "Install Headroom first, then reload pi. Example: curl -fsSL https://raw.githubusercontent.com/chopratejas/headroom/main/scripts/install.sh | bash";
    case "win32":
      return "Install Headroom first, then reload pi. Example: irm https://raw.githubusercontent.com/chopratejas/headroom/main/scripts/install.ps1 | iex";
    default:
      return "Install Headroom first and ensure `headroom` command is available on PATH, then reload pi.";
  }
}

function detectHeadroomInstallProblem(): string | undefined {
  const result = spawnSync(HEADROOM_BIN, ["--help"], {
    stdio: "ignore",
  });
  if (!result.error) return undefined;
  const detail =
    result.error instanceof Error ? result.error.message : String(result.error);
  return `Headroom CLI not found via ${JSON.stringify(HEADROOM_BIN)}. ${detectPlatformInstallHint()} (${detail})`;
}

function notifyHeadroomUnavailable(
  ctx: ExtensionCtx,
  model: ProviderModel | undefined = ctx.model,
  opts: { once?: boolean } = {},
): void {
  const provider = managedProviderFor(model);
  if (!provider || !headroomInstallProblem) return;

  const state = globalState();
  if (opts.once && state.installWarningShown) return;
  if (opts.once) state.installWarningShown = true;

  ctx.ui.notify(
    `Headroom unavailable for ${provider}; using pi defaults. ${headroomInstallProblem}`,
    "warn",
  );
}

async function probeUrl(url: string): Promise<boolean> {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), PROBE_TIMEOUT_MS);
  try {
    const response = await fetch(url, {
      method: "GET",
      signal: controller.signal,
    });
    return response.ok;
  } catch {
    return false;
  } finally {
    clearTimeout(timer);
  }
}

async function probeLiveness(rootUrl: string): Promise<boolean> {
  for (const path of ["/livez", "/readyz", "/health"]) {
    if (await probeUrl(`${rootUrl}${path}`)) return true;
  }
  return false;
}

function probePortBindable(port: number): Promise<boolean> {
  return new Promise((resolve) => {
    const server = createServer();
    let settled = false;

    server.once("error", () => {
      if (settled) return;
      settled = true;
      resolve(false);
    });

    server.once("listening", () => {
      server.close(() => {
        if (settled) return;
        settled = true;
        resolve(true);
      });
    });

    server.listen(port, DEFAULT_HOST);
  });
}

async function assessPort(
  provider: ManagedProvider,
  port: number,
): Promise<PortAssessment> {
  const config = buildManagedProxyConfig(provider, port, DEFAULT_HOST);
  if (await probeLiveness(config.rootUrl)) {
    return { disposition: "headroom", config };
  }
  if (await probePortBindable(port)) {
    return { disposition: "free", config };
  }
  return { disposition: "occupied", config };
}

async function resolveInitialConfig(
  provider: ManagedProvider,
): Promise<ManagedProxyConfig> {
  const preferredPort = preferredPortFor(provider);
  const savedRoute = loadRoute(provider);
  const candidatePorts: number[] = [];

  const addCandidate = (port: number | undefined) => {
    if (!port || port <= 0 || candidatePorts.includes(port)) return;
    candidatePorts.push(port);
  };

  addCandidate(savedRoute?.port);
  addCandidate(preferredPort);
  for (let offset = 1; offset <= PORT_SCAN_LIMIT; offset += 1) {
    addCandidate(preferredPort + offset);
  }

  let preferredOccupied: PortAssessment | undefined;
  for (const port of candidatePorts) {
    const assessment = await assessPort(provider, port);
    if (
      assessment.disposition === "headroom" ||
      assessment.disposition === "free"
    ) {
      saveRoute(assessment.config);
      return assessment.config;
    }
    if (!preferredOccupied && port === preferredPort) {
      preferredOccupied = assessment;
    }
  }

  const fallback =
    preferredOccupied?.config ??
    buildManagedProxyConfig(provider, preferredPort, DEFAULT_HOST);
  saveRoute(fallback);
  return fallback;
}

async function initializeConfigs(): Promise<
  Record<ManagedProvider, ManagedProxyConfig>
> {
  if (resolvedConfigs) return resolvedConfigs;
  if (initPromise) return initPromise;

  initPromise = (async () => {
    const entries = await Promise.all(
      providerIds().map(
        async (provider) =>
          [provider, await resolveInitialConfig(provider)] as const,
      ),
    );
    resolvedConfigs = Object.fromEntries(entries) as Record<
      ManagedProvider,
      ManagedProxyConfig
    >;
    return resolvedConfigs;
  })();

  return initPromise;
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function waitForReady(
  config: ManagedProxyConfig,
  proxy: ManagedProxyState,
): Promise<void> {
  const startedAt = Date.now();
  while (Date.now() - startedAt < START_TIMEOUT_MS) {
    if (await probeLiveness(config.rootUrl)) {
      markHealthy(proxy);
      return;
    }
    if (
      proxy.process?.exitCode !== null &&
      proxy.process?.exitCode !== undefined
    ) {
      throw new Error(
        `headroom proxy exited early with code ${proxy.process.exitCode}`,
      );
    }
    await sleep(PROBE_INTERVAL_MS);
  }
  throw new Error(
    `Timed out waiting for ${config.provider} proxy at ${config.rootUrl}`,
  );
}

function markHealthy(proxy: ManagedProxyState): ManagedProxyState {
  proxy.status = proxy.owned ? "running" : "external";
  proxy.lastHealthyAt = Date.now();
  proxy.lastError = undefined;
  return proxy;
}

function isFreshHealthy(
  proxy: ManagedProxyState | undefined,
): proxy is ManagedProxyState {
  return (
    !!proxy?.lastHealthyAt && Date.now() - proxy.lastHealthyAt < HEALTH_TTL_MS
  );
}

function spawnProxy(config: ManagedProxyConfig): ManagedProxyState {
  const child = spawn(
    HEADROOM_BIN,
    ["proxy", "--host", DEFAULT_HOST, "--port", String(config.port)],
    {
      env: {
        ...process.env,
        ...config.env,
      },
      detached: true,
      stdio: "ignore",
    },
  );

  const proxy: ManagedProxyState = {
    provider: config.provider,
    port: config.port,
    rootUrl: config.rootUrl,
    routedBaseUrl: config.routedBaseUrl,
    owned: true,
    pid: child.pid,
    process: child,
    status: "starting",
  };

  child.on("error", (error: Error) => {
    proxy.status = "failed";
    proxy.lastError = error.message;
  });
  child.on("exit", (code: number | null, signal: string | null) => {
    proxy.process = undefined;
    proxy.status = "stopped";
    proxy.lastHealthyAt = undefined;
    proxy.lastError = signal
      ? `process exited via signal ${signal}`
      : code === 0
        ? undefined
        : `process exited with code ${code ?? "unknown"}`;
  });
  child.unref();

  return proxy;
}

async function resolveKnownState(
  provider: ManagedProvider,
): Promise<ManagedProxyState | undefined> {
  const state = globalState();
  const cached = state.proxies.get(provider);
  if (cached && (await probeLiveness(cached.rootUrl))) {
    return markHealthy(cached);
  }

  const config = getConfig(provider);
  const owner = loadOwner(provider);
  const healthy = await probeLiveness(config.rootUrl);

  if (
    healthy &&
    owner &&
    owner.port === config.port &&
    processAlive(owner.pid)
  ) {
    const owned = markHealthy({
      ...buildBaseState(config, true),
      pid: owner.pid,
    });
    state.proxies.set(provider, owned);
    return owned;
  }

  if (healthy) {
    const external = markHealthy(buildBaseState(config, false));
    state.proxies.set(provider, external);
    if (owner && !processAlive(owner.pid)) clearOwner(provider);
    return external;
  }

  if (owner && !processAlive(owner.pid)) clearOwner(provider);
  return cached;
}

async function ensureProxyRunning(
  provider: ManagedProvider,
): Promise<ManagedProxyState> {
  const state = globalState();
  const existing = state.proxies.get(provider);
  if (isFreshHealthy(existing)) return existing;

  const pending = state.pending.get(provider);
  if (pending) return pending;

  const config = getConfig(provider);
  const promise = (async () => {
    const known = await resolveKnownState(provider);
    if (known && known.status !== "stopped" && known.status !== "failed") {
      return known;
    }

    if (!AUTOSTART) {
      throw new Error(
        `No healthy Headroom proxy for ${provider} at ${config.rootUrl}. Start it manually or enable PI_HEADROOM_AUTOSTART.`,
      );
    }

    const assessment = await assessPort(provider, config.port);
    if (assessment.disposition === "occupied") {
      throw new Error(
        `Selected port ${config.port} for ${provider} is occupied by a non-Headroom service. Reload pi to rescan fallback ports.`,
      );
    }
    if (assessment.disposition === "headroom") {
      const external = markHealthy(buildBaseState(config, false));
      state.proxies.set(provider, external);
      return external;
    }

    const spawned = spawnProxy(config);
    state.proxies.set(provider, spawned);
    try {
      await waitForReady(config, spawned);
      saveOwner(config, spawned);
      return spawned;
    } catch (error) {
      spawned.status = "failed";
      spawned.lastError =
        error instanceof Error ? error.message : String(error);
      clearOwner(provider);
      throw error;
    }
  })();

  state.pending.set(provider, promise);
  try {
    return await promise;
  } finally {
    state.pending.delete(provider);
  }
}

async function terminateProxy(proxy: ManagedProxyState): Promise<void> {
  if (!proxy.owned || !proxy.pid) return;

  try {
    process.kill(proxy.pid, "SIGTERM");
  } catch {
    clearOwner(proxy.provider);
    proxy.status = "stopped";
    proxy.lastHealthyAt = undefined;
    proxy.process = undefined;
    return;
  }

  const deadline = Date.now() + 3000;
  while (Date.now() < deadline) {
    if (!(await probeLiveness(proxy.rootUrl))) {
      clearOwner(proxy.provider);
      proxy.status = "stopped";
      proxy.lastHealthyAt = undefined;
      proxy.process = undefined;
      return;
    }
    await sleep(150);
  }

  try {
    process.kill(proxy.pid, "SIGKILL");
  } catch {
    // already gone
  }

  clearOwner(proxy.provider);
  proxy.status = "stopped";
  proxy.lastHealthyAt = undefined;
  proxy.process = undefined;
}

async function cleanupOwnedProxies(): Promise<void> {
  const state = globalState();
  if (state.cleaningUp) return;
  state.cleaningUp = true;

  const owned = Array.from(state.proxies.values()).filter(
    (proxy) => proxy.owned,
  );
  await Promise.allSettled(owned.map((proxy) => terminateProxy(proxy)));

  for (const proxy of owned) {
    state.proxies.delete(proxy.provider);
    state.pending.delete(proxy.provider);
  }
}

function installProcessExitCleanup(): void {
  if (SHUTDOWN_MODE !== "session") return;
  const state = globalState();
  if (state.cleanupInstalled) return;
  state.cleanupInstalled = true;
  process.once("exit", () => {
    for (const proxy of state.proxies.values()) {
      if (!proxy.owned || !proxy.pid) continue;
      try {
        process.kill(proxy.pid, "SIGTERM");
      } catch {
        // ignore best-effort exit cleanup
      }
      clearOwner(proxy.provider);
    }
  });
}

async function ensureForCurrentModel(
  model: ProviderModel | undefined,
): Promise<void> {
  const provider = managedProviderFor(model);
  if (!provider) return;
  await ensureProxyRunning(provider);
}

function warmInBackground(
  model: ProviderModel | undefined,
  ctx: ExtensionCtx,
  source: string,
): void {
  const provider = managedProviderFor(model);
  updateUiStatus(ctx, model);
  if (!provider) return;
  if (headroomInstallProblem) {
    if (VERBOSE) notifyHeadroomUnavailable(ctx, model);
    return;
  }

  void ensureProxyRunning(provider)
    .then(async () => {
      await refreshPerfSummary(provider);
      updateUiStatus(ctx, model);
      if (VERBOSE) {
        ctx.ui.notify(
          `Headroom proxy ready for ${provider} (${source})`,
          "info",
        );
      }
    })
    .catch((error) => {
      updateUiStatus(ctx, model);
      ctx.ui.notify(
        `Headroom background start failed for ${provider}: ${error instanceof Error ? error.message : String(error)}`,
        "error",
      );
    });
}

function parseProviderArg(
  raw: string | undefined,
): ManagedProvider | "all" | undefined {
  const value = raw?.trim().toLowerCase();
  if (!value) return undefined;
  if (value === "all") return "all";
  return providerIds().includes(value as ManagedProvider)
    ? (value as ManagedProvider)
    : undefined;
}

async function ownedStateFor(
  provider: ManagedProvider,
): Promise<ManagedProxyState | undefined> {
  const state = globalState();
  const current = state.proxies.get(provider);
  if (current?.owned) return current;

  const owner = loadOwner(provider);
  if (!owner || !processAlive(owner.pid)) {
    clearOwner(provider);
    return undefined;
  }

  const config = getConfig(provider);
  const proxy = buildBaseState(config, true);
  proxy.pid = owner.pid;
  if (await probeLiveness(config.rootUrl)) {
    markHealthy(proxy);
  }
  state.proxies.set(provider, proxy);
  return proxy;
}

function registerCommands(pi: ExtensionAPI): void {
  pi.registerCommand(STATUS_COMMAND, {
    description: "Show Headroom proxy routing and supervisor status.",
    handler: async (_args: string, ctx: ExtensionCtx) => {
      await Promise.all(
        providerIds().map((provider) => resolveKnownState(provider)),
      );
      const activeProvider = managedProviderFor(ctx.model);
      if (activeProvider) {
        await refreshPerfSummary(activeProvider, { fresh: true });
      }
      updateUiStatus(ctx);
      ctx.ui.notify(statusLines(ctx.model).join("\n"), "info");
    },
  });

  pi.registerCommand(STOP_COMMAND, {
    description:
      "Stop extension-owned Headroom proxies. Usage: /headroom-stop [provider|all]",
    handler: async (args: string, ctx: ExtensionCtx) => {
      if (headroomInstallProblem) {
        updateUiStatus(ctx);
        ctx.ui.notify(
          `Headroom unavailable; managed providers are using pi defaults. ${headroomInstallProblem}`,
          "warn",
        );
        return;
      }

      if (headroomInstallProblem) {
        updateUiStatus(ctx);
        ctx.ui.notify(
          `Headroom unavailable; managed providers are using pi defaults. ${headroomInstallProblem}`,
          "warn",
        );
        return;
      }

      const selected = parseProviderArg(args);
      if (args.trim() && !selected) {
        const known = [...providerIds(), "all"].join(", ");
        ctx.ui.notify(
          `Unknown provider ${JSON.stringify(args.trim())}. Use ${known}.`,
          "error",
        );
        return;
      }

      const providers =
        selected && selected !== "all" ? [selected] : providerIds();
      const stopped: ManagedProvider[] = [];

      for (const provider of providers) {
        const proxy = await ownedStateFor(provider);
        if (!proxy) continue;
        await terminateProxy(proxy);
        globalState().proxies.delete(provider);
        globalState().perf.delete(provider);
        stopped.push(provider);
      }

      updateUiStatus(ctx);
      ctx.ui.notify(
        stopped.length
          ? `Stopped Headroom proxy for ${stopped.join(", ")}.`
          : "No extension-owned Headroom proxy to stop.",
        "info",
      );
    },
  });

  pi.registerCommand(RESTART_COMMAND, {
    description:
      "Restart extension-owned Headroom proxies. Usage: /headroom-restart [provider|all]",
    handler: async (args: string, ctx: ExtensionCtx) => {
      if (headroomInstallProblem) {
        updateUiStatus(ctx);
        ctx.ui.notify(
          `Headroom unavailable; managed providers are using pi defaults. ${headroomInstallProblem}`,
          "warn",
        );
        return;
      }

      const selected = parseProviderArg(args);
      if (args.trim() && !selected) {
        const known = [...providerIds(), "all"].join(", ");
        ctx.ui.notify(
          `Unknown provider ${JSON.stringify(args.trim())}. Use ${known}.`,
          "error",
        );
        return;
      }

      const providers =
        selected && selected !== "all" ? [selected] : providerIds();
      for (const provider of providers) {
        const proxy = await ownedStateFor(provider);
        if (proxy) {
          await terminateProxy(proxy);
          globalState().proxies.delete(provider);
          globalState().perf.delete(provider);
        }
        await ensureProxyRunning(provider);
        await refreshPerfSummary(provider);
      }

      updateUiStatus(ctx);
      ctx.ui.notify(
        `Restarted Headroom proxy for ${providers.join(", ")}.`,
        "info",
      );
    },
  });
}

export default async function headroomProviderSupervisor(
  pi: ExtensionAPI,
): Promise<void> {
  headroomInstallProblem = detectHeadroomInstallProblem();
  await initializeConfigs();
  installProcessExitCleanup();
  if (!headroomInstallProblem) {
    registerManagedProviders(pi, getConfig);
  }
  registerCommands(pi);

  pi.on("session_start", async (_event: unknown, ctx: ExtensionCtx) => {
    updateUiStatus(ctx);
    if (headroomInstallProblem) {
      notifyHeadroomUnavailable(ctx, ctx.model, { once: true });
      return;
    }
    warmInBackground(ctx.model, ctx, "session_start");
  });

  pi.on("model_select", async (event: ModelSelectEvent, ctx: ExtensionCtx) => {
    updateUiStatus(ctx, event.model);
    if (headroomInstallProblem) {
      notifyHeadroomUnavailable(ctx, event.model, { once: true });
      return;
    }
    warmInBackground(event.model, ctx, "model_select");
  });

  pi.on("before_agent_start", async (_event: unknown, ctx: ExtensionCtx) => {
    if (headroomInstallProblem) {
      updateUiStatus(ctx);
      return;
    }
    try {
      updateUiStatus(ctx);
      await ensureForCurrentModel(ctx.model);
      const provider = managedProviderFor(ctx.model);
      if (provider) {
        await refreshPerfSummary(provider);
      }
      updateUiStatus(ctx);
    } catch (error) {
      updateUiStatus(ctx);
      ctx.ui.notify(
        `Headroom route unavailable: ${error instanceof Error ? error.message : String(error)}`,
        "error",
      );
      throw error;
    }
  });

  pi.on("agent_end", async (_event: unknown, ctx: ExtensionCtx) => {
    if (headroomInstallProblem) {
      updateUiStatus(ctx);
      return;
    }

    const provider = managedProviderFor(ctx.model);
    if (!provider) {
      updateUiStatus(ctx);
      return;
    }

    await refreshPerfSummary(provider, { fresh: true });
    updateUiStatus(ctx);
  });

  pi.on("session_shutdown", async (event: SessionShutdownEvent) => {
    if (SHUTDOWN_MODE !== "session") return;
    if (event.reason !== "quit") return;
    await cleanupOwnedProxies();
  });
}

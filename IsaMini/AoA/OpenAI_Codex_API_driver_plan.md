# Plan — `OpenAI-Codex-API` driver (ChatGPT-subscription gpt-5.5 via the `openai-oauth` proxy)

Status: **APPROVED — implementing.** Date: 2026-06-23.
Folds in: the 12 surviving adversarial-review concerns + user directives
(strict_tools=False; reasoning NEVER dropped; fail-fast via a NEW `ResourceUnavailable` quit reason).

---

## 1. Goal & route

New AoA driver `@agent_driver("OpenAI-Codex-API")` driving `gpt-5.5` on the **ChatGPT-subscription
codex backend**, reusing the existing OpenAI Responses machinery in `driver_api.py`.

Why: the `Codex` (`codex exec`) driver runs a **lossy 4 KB tool-schema compaction** that strips our
`edit` tool's big schema down to `{}`. We bypass codex entirely.

**Route = local proxy `EvanZhouDev/openai-oauth`** (decided):
- Reads `~/.codex/auth.json`, **owns the OAuth lifecycle** (auto-refresh + rotation). ⇒ the driver
  carries **ZERO auth code**, and **we do NOT refresh tokens**.
- Exposes `http://127.0.0.1:10531/v1`, **no API key required**.
- Forwards a **native `/v1/responses`** body near-verbatim (shallow copy; sets instructions/store/
  stream; deletes `max_output_tokens`; **never rewrites `tools`**). Stateless: hard-rejects
  `previous_response_id`.
- **HARD route rule: only ever hit `/v1/responses`.** The proxy's `/v1/chat/completions` re-translates
  `tools` (Vercel `ai` SDK) → schema loss. `OpenAIResponsesProvider` already uses `responses.create`,
  so this holds by construction.

## 2. Probe evidence (against the live codex backend; all read-only, no secrets)

- **probe-1** — strict `anyOf` tool accepted faithfully; conformant args. 200.
- **probe-2** — stateless multi-turn (resend `function_call`+`function_call_output`, no
  `previous_response_id`, store:false) → 200.
- **probe-3** — `previous_response_id` over HTTP → 400 "Unsupported parameter" ⇒ stateless mandatory.
- **probe-4** — `prompt_cache_retention` → 400; `max_output_tokens` → 400; `prompt_cache_key` → 200.
- **probe-5** — `background:true` (non-stream) → 400 "Stream must be set to true".
- **probe-6** — at `effort:high` **with `tool_choice:"required"`** the backend returned **0 reasoning
  items**; stateless turn-2 → 200. CAVEAT: forced tool_choice may suppress reasoning; real AoA turns do
  **not** force tool_choice, so they MAY emit reasoning. Resending encrypted reasoning is **backend-
  supported by construction** (codex itself runs store:false + resends encrypted reasoning every turn).

Pin the provider overrides in §4; route-independent (the proxy forwards
`prompt_cache_retention`/`previous_response_id`/reasoning verbatim; only strips `max_output_tokens`).

## 3. Locked decisions

- **D1.** Route = the `openai-oauth` proxy (§1).
- **D2.** **No token refresh / no `auth.json` in the driver.** Proxy owns it.
- **D3.** New driver **subclasses `APIDriver_ChatGPT`**, registered **`"OpenAI-Codex-API"`**. `ChatGPT`
  is **NOT renamed** ⇒ no alias work, no fixture migration.
- **D4.** Override form = **class attributes** on `OpenAIResponsesProvider` (defaults == current
  `ChatGPT` behavior); `CodexResponsesProvider` overrides them. `chat` reads them — no `if stateless`.
- **D5.** Proxy lifecycle = **pure launcher-owned** (§6). The driver does **NOT** auto-start the proxy;
  if unreachable it **fails fast** (D8). Single-machine `by aoa`: the user runs `npx openai-oauth`.
- **D6.** **`strict_tools = False`** (parity with `ChatGPT` — inherited, not set; we don't rely on
  strict tools). The `edit` tool ships its raw `$ref` schema non-strict, **identical to the working
  `ChatGPT` driver**. strict-FLAT is a **one-flag, probe-1-proven fallback** *iff* §7 e2e shows the
  codex backend mishandles the raw schema. C2 (system prompt) likewise **inherits `ChatGPT`** (developer
  input item); `SYSTEM_AS_INSTRUCTIONS` is only a documented fallback (§8), NOT implemented now.
- **D7.** **Reasoning items are NEVER stripped.** `include:["reasoning.encrypted_content"]` stays ON;
  `_msgs_to_input` resends `native` (incl. reasoning) verbatim — codex-faithful. If the backend ever
  rejects resent reasoning, the existing non-retryable `BadRequestError` path **crashes loudly** (no
  silent drop). Context **compaction** (`_compact`) is **exempt** (user-confirmed 2026-06-23): only the
  per-turn resend is guaranteed to keep reasoning. `_compact` unchanged.
- **D8.** **Fatal proxy failure → a NEW terminal `quit_info` variant `ResourceUnavailable`**
  (`reason="resource_unavailable"`), distinct from `ResourceExhausted` (budget/retry exhaustion).
  `chat` raises an in-band `LMUnreachable(AoA_Error)`; the driver/executor convert it to
  `quit_info = ResourceUnavailable(detail=…)` so `run()` returns normally → `toplevel` reports the
  reason cleanly. **NO raw exception escapes** (a fork's exception would otherwise hit
  `ToolExecutor.execute`'s `except Exception: sys.exit(1)` → `SystemExit` kills the host). **ML side =
  zero change** (verified: `agent_server.ML:1404` passes `reason` through to `Agent_Give_Up` as an
  opaque string; no per-value match).

## 4. Change list (symbol anchors, not line numbers)

### 4.1 `OpenAIResponsesProvider` — overridable class-attr policy (defaults = today's behavior)

Add 7 ClassVars (each default == current hardcoded behavior, so `ChatGPT` is byte-identical):

```python
class OpenAIResponsesProvider(OpenAIBase):
    STORE                     = True
    SEND_PREVIOUS_RESPONSE_ID = True
    SURFACE_RESPONSE_ID       = True
    SEND_CACHE_RETENTION      = True
    SEND_MAX_OUTPUT_TOKENS    = True
    BACKGROUND_FALLBACK       = True
    FAIL_FAST_NON_TRANSIENT   = False   # [C11/C12] conn-refused / 401 -> LMUnreachable
```

Make `chat` **read** them:
- `params["store"] = self.STORE`
- `if self.SEND_CACHE_RETENTION: params["prompt_cache_retention"] = "24h"`
- `if self.SEND_MAX_OUTPUT_TOKENS and self.max_output_tokens is not None: params["max_output_tokens"] = …`
- `if self.SEND_PREVIOUS_RESPONSE_ID and previous_response_id is not None: params["previous_response_id"] = …`
- return `response_id = response.id if self.SURFACE_RESPONSE_ID else None`
- **background**: at BOTH `_resubmit_background` call sites, gate on `self.BACKGROUND_FALLBACK`; when
  off, treat as a transient retry (`attempt+=1; sleep; continue`).
- **[C11/C12] fail-fast → `LMUnreachable`**: add a small helper `_fail_fast(e)` that raises
  `LMUnreachable` with the right user-supplied detail (creds vs proxy-down). Guard it at the TOP of
  BOTH existing handlers: the create-site `except openai.APIError` AND the streaming-site
  `except (openai.APIError, httpx.TransportError)` —
  `if self.FAIL_FAST_NON_TRANSIENT and isinstance(e, (openai.APIConnectionError, openai.AuthenticationError)): self._fail_fast(e)`.
  (Both are `APIError` subclasses, so this needs no new except clause; 429 stays transient because
  `RateLimitError` is caught earlier.) Flag `False` ⇒ unchanged retry path.
- **KEEP unchanged**: `include = ["reasoning.encrypted_content"]` (D7); `prompt_cache_key`; the
  reasoning resend in `_msgs_to_input` (D7 — do NOT strip).

`_fail_fast` (user-approved wording):
```python
def _fail_fast(self, e):
    if isinstance(e, openai.AuthenticationError):
        raise LMUnreachable(
            "OpenAI-Codex-API: ChatGPT subscription credentials invalid/expired. "
            "Run `codex login` and retry.") from e
    raise LMUnreachable(
        f"OpenAI-Codex-API: local openai-oauth proxy unreachable at {self._client.base_url}. "
        "Start it (e.g. `npx openai-oauth`) and retry.") from e
```

The shared **loop** (`_api_loop`/`_run_fork`) request-body path needs no change; the shared **`chat`**
gets the reads above; the fail-fast handling lives in `chat` + §4.4.

### 4.2 New `CodexResponsesProvider(OpenAIResponsesProvider)`

```python
class CodexResponsesProvider(OpenAIResponsesProvider):
    STORE                     = False   # codex backend
    SEND_PREVIOUS_RESPONSE_ID = False   # probe-3 (400) -> full transcript each turn
    SURFACE_RESPONSE_ID       = False   # response_id None -> loop/fork resend full
    SEND_CACHE_RETENTION      = False   # probe-4 (400)
    SEND_MAX_OUTPUT_TOKENS    = False   # probe-4 (400)
    BACKGROUND_FALLBACK       = False   # probe-5 (400; backend requires stream=true)
    FAIL_FAST_NON_TRANSIENT   = True    # [C11/C12] proxy down/401 -> LMUnreachable

    def _supports_allowed_tools_choice(self):   # reuse existing seam
        return False   # allowed_tools object form untested on this backend; conservative
```

- **strict_tools**: NOT set ⇒ inherits `False` (D6). Sends the identical raw schema as `ChatGPT`.
- **System prompt**: inherits `ChatGPT` (developer input item) — D6; no `SYSTEM_AS_INSTRUCTIONS`.
- **Reasoning**: `include` ON, resend unchanged (D7).
- **Shared loop unchanged**: `SURFACE_RESPONSE_ID=False` ⇒ `response_id=None` ⇒ `_last_response_id`/
  `fork_response_id` stay None ⇒ `_api_loop`/`_run_fork` resend the full `self._messages` each turn
  (verified; `_msgs_sent_through` stays 0; fork lands in its "No stored response" full-copy arm).

### 4.3 New driver `APIDriver_OpenAICodex(APIDriver_ChatGPT)`

```python
@agent_driver("OpenAI-Codex-API")
class APIDriver_OpenAICodex(APIDriver_ChatGPT):
    DEFAULT_MODEL      = "gpt-5.5"
    FORK_CHEAPER_MODEL = None   # [C1] disable the cheaper-fork branch
```

- **[C1]** `FORK_CHEAPER_MODEL=None` makes `APIDriver_ChatGPT._fork_provider`'s
  `FORKING_CHEAPER_NO_CTXT` guard falsy ⇒ it returns `self._provider` (the proxy-configured
  `CodexResponsesProvider`) for **every** fork mode. **No `_fork_provider` override needed**; no second
  provider is built at the real `api.openai.com`.
- Override **only `__init__`** to build `CodexResponsesProvider(...)` with:
  - `base_url = os.environ.get("OPENAI_OAUTH_BASE_URL", "http://127.0.0.1:10531/v1")`
  - `api_key = "openai-oauth-local"` (proxy needs none; the SDK requires a non-empty string)
  - `cache_key = f"proof-{uuid4}"`, `reasoning_effort` from `_parse_effort_suffix` (mirror ChatGPT).
  - **do NOT** pass `strict_tools` (D6).
- Inherit `_retry_transient` (no-op), `estimate_tokens`, `__str__`, `_fork_provider`. No
  `default_headers`, no `auth.json`, no refresh (proxy injects auth).

### 4.4 Fatal LM-unreachable → `ResourceUnavailable` quit (no raw escape) [C13, D8] — VERIFIED

`model.py` additions:
- `class LMUnreachable(AoA_Error)` — in-band signal from `chat` (a Provider can't set `quit_info`).
- `@dataclass class ResourceUnavailable` — `reason: ClassVar[str] = "resource_unavailable"`,
  `is_terminal: ClassVar[bool] = True`, `detail: str | None = None`; add to the `QuitInfo` union.

Conversion to `quit_info = ResourceUnavailable(detail=str(e))` on BOTH paths (`run()` returns
normally, no exception escapes, no `sys.exit`, debug-safe):
- **Main loop** (`_api_loop`): wrap the `chat` call; `except LMUnreachable as e: self.quit_info =
  ResourceUnavailable(detail=str(e)); break`. Terminal ⇒ the outer
  `if not isinstance(self.quit_info, (Restart, Refresh)): break` ends the loop.
- **Fork / tool path** (`mcp_http_server.py ToolExecutor.execute`): add `except LMUnreachable as e:` as
  the FIRST except (before `except (ConnectionError, EOFError)` and before `except Exception:
  sys.exit(1)`) → `self._session.quit_info = ResourceUnavailable(detail=str(e))` and
  `return (str(e), True)`. `_execute_tool_calls` appends it; `_api_loop` then hits
  `if self.quit_info is not None: break`. `_run_fork` needs **no** change.

VERIFIED chain (fork): `fork chat → _run_fork → tool coro → Task → _race_outbox task.result() →
_run_tool_via_channel except BaseException: raise → execute() (new) except LMUnreachable`.
VERIFIED `rpc.py:303 except Exception` is host-survivable in non-debug; `sys.exit(1)`'s `SystemExit`
(BaseException) is NOT — hence we convert to `quit_info` rather than let the fork raise.

### 4.5 Pricing / accounting
Flat-rate subscription ⇒ USD is an **estimate** (document, like `Codex`). Reuse the `gpt-5.5` PRICING
entry. No code change beyond a doc note.

## 5. Robustness — graceful give-up (Option A, no `connection.warning`)
Proxy not running → `APIConnectionError`; creds expired → 401 `AuthenticationError`.
`FAIL_FAST_NON_TRANSIENT=True` makes `chat` raise `LMUnreachable` (no 1-hour spin); §4.4 converts it to
`quit_info = ResourceUnavailable` on both paths → `toplevel` reports `resource_unavailable` + the
user-supplied `detail` (host survives, debug-safe, no `sys.exit`). 429 stays transient;
`BadRequestError` stays non-retryable. No `connection.warning`, no `Runtime.connection`; `model.py`
changes = `LMUnreachable` + `ResourceUnavailable` only.

## 6. Operational — proxy lifecycle is launcher-owned (D5)
- **Fleet** (`run_fleet_eval.sh` / `stop_fleet_eval.sh`, single Python process, ~24 majors):
  - `run_fleet_eval.sh`: start `npx openai-oauth` **once** next to the existing port pre-checks; record
    its pid + port to `state_fleet` (e.g. `proxy.pid` / `proxy.port`).
  - `stop_fleet_eval.sh`: teardown stanza killing the recorded pid + exact-port LISTENer (same surgical
    **never-`pkill -f`** discipline as the RPC host).
  - (C6) multi-process `auth.json` write-race framing **dropped** — topology is single-process.
- **Single machine** (`by aoa`): user runs `npx openai-oauth` first.
- **Driver**: does NOT spawn/manage the proxy; unreachable → fail-fast (§5).
- (Shell-script edits, separate from `driver_api.py`.)

## 7. Verification (after implementation, before any commit)
1. Restart the REPL / launcher to reload edited Python (no `.ML` change).
2. Start `npx openai-oauth`; readiness via a **TCP connect probe on 127.0.0.1:10531** (NOT
   `GET /v1/models`; C8).
3. **e2e**: `by aoa` with `agent_AoA_driver="OpenAI-Codex-API.gpt-5.5-high"`. Confirm: `edit` fires
   with the **non-strict raw** schema (D6/C3); proof progresses; multi-turn full-resend works.
4. **Reasoning round-trip** (D7): at real effort with **unforced** tool_choice, confirm resending
   emitted reasoning items returns 200. If rejected → loud crash by design; then a targeted fix (never
   a silent strip).
5. **[C2]** Confirm the developer-item system prompt is honored on the codex backend.
6. **[C13/D8]** Stop the proxy (a) before start and (b) mid-fork → both confirm a clean
   `resource_unavailable` give-up (`run()` returns), NOT a 1-hour spin and NOT a `sys.exit(1)`. Test
   with `ISABELLE_RPC_DEBUG=1` too (must not crash).
7. **No `ChatGPT` regression**: the 7 defaults == old behavior; spot-check `store=True` /
   `previous_response_id` still sent, `strict_tools` default unchanged.

## 8. Out of scope / documented fallbacks
- Renaming `ChatGPT`, alias migration (D3).
- `auth.json` read / refresh / write-back, flock, keyring (D2).
- **Stripping reasoning items** (explicitly rejected — D7).
- `ClaudeCode` and `Codex` (`codex exec`) drivers — untouched.
- **Fallbacks if §7 e2e fails** (NOT implemented now): `strict_tools=True` (probe-1-proven flat strict
  schema) if the raw schema misbehaves; `SYSTEM_AS_INSTRUCTIONS` (route SystemMsg → top-level
  `instructions`) if the developer-item system prompt is ignored.

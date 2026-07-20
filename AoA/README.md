# AoA — an AI proof agent for Isabelle/HOL

AoA (Agent over AST) is a proof agent for Isabelle, built on Minilang. It comes as an ordinary proof method: write by aoa wherever you would write by auto or by blast, and everything from there is automatic and transparent. If the goal itself is flawed — not provable as stated — AoA will tell you that, too.

---

## 1. Installation

```bash
conda create -n <YOUR_ENV> -c https://conda.qiyuan.me -c conda-forge isabelle-ai
```

---

## 2. Quick start

Run:
```bash
conda activate <YOUR_ENV>
isabelle jedit
```
and then type:
```isabelle
theory Scratch
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

theorem sqrt2_not_rational: "sqrt 2 ∉ ℚ" by aoa

end
```

---

## 3. Choosing a model and providing credentials

Pick the driver with the `AoA_driver` attribute:

```isabelle
declare [[AoA_driver = "ChatGPT.gpt-5.5-high"]]
```

Put it anywhere before the `by aoa` that should use it — at the top of the
theory to apply to the whole file, or inside a `context`/proof block for a
narrower scope.

### Driver string syntax

```
<DriverName>              — the driver's default model
<DriverName>.<argument>   — the driver's own argument, usually a model id
```

The string is split at the **first dot only**, so the argument may itself
contain dots (`ChatGPT.gpt-5.5-pro`). Driver names are **case-sensitive**:
`claudecode` is not `ClaudeCode`.

Four drivers are covered below. `ClaudeCode` is the default and is what you get
if you never set the attribute at all.

### Where to put API keys

Credentials go in your personal Isabelle settings file:

```bash
isabelle getenv -b ISABELLE_HOME_USER    # prints e.g. /home/you/.isabelle/Isabelle2025-2
```

Edit `$(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings` and add plain
assignments — Isabelle sources this file with auto-export on, so a bare
assignment is enough and `export` is not needed:

```bash
OPENAI_API_KEY=sk-...
DEEPSEEK_API_KEY=sk-...
```

Check that a variable really arrived:

```bash
isabelle getenv -a | grep OPENAI_API_KEY
```

> **After editing `etc/settings`, restart Isabelle.** The settings environment is
> captured once at startup. If AoA has already run in this session, also stop the
> background helper process so it is relaunched with the new environment:
> `pkill -f fork_and_launch__`.

---

### 3.1 `ClaudeCode` — Claude via the Claude Code CLI *(default)*

The default driver. It does **not** use an API key: it delegates authentication
to the Claude Code CLI, which you must install and log into yourself.

```bash
npm install -g @anthropic-ai/claude-code
claude          # then run /login
```

If you skip this, AoA stops with:

```
Claude-Code: the CLI is not authenticated. Run `claude` and use /login, then retry.
```

The argument is a Claude model id, optionally carrying a **context-window
suffix** `[1m]` or `[200k]`:

```isabelle
declare [[AoA_driver = "ClaudeCode"]]                        (* default: claude-opus-4-8[1m] *)
declare [[AoA_driver = "ClaudeCode.claude-opus-4-8[1m]"]]
declare [[AoA_driver = "ClaudeCode.claude-sonnet-4-6[200k]"]]
```

> The suffix is how AoA learns the context size, and it is **not** inferred from
> the model id. A model id written without a suffix is assumed to have a 200k
> window, so `ClaudeCode.claude-opus-4-8` will compact far earlier than the
> model actually requires — write `[1m]` when the model supports it.

This driver takes no reasoning-effort suffix.

---

### 3.2 `ChatGPT` — GPT via the OpenAI API

Needs an OpenAI API key:

```bash
# $(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings
OPENAI_API_KEY=sk-...
```

The argument is a model id, optionally with a **reasoning-effort suffix** —
one of `-low`, `-medium`, `-high`, `-xhigh`, `-max`. Without a suffix the
effort is `medium`.

```isabelle
declare [[AoA_driver = "ChatGPT"]]                  (* gpt-5.5, medium effort *)
declare [[AoA_driver = "ChatGPT.gpt-5.5-high"]]
declare [[AoA_driver = "ChatGPT.gpt-5.5-xhigh"]]
declare [[AoA_driver = "ChatGPT.gpt-5.5-pro-high"]]
```

If the key is missing, the driver fails on startup with the OpenAI SDK's own
message: *"The api_key client option must be set …"*.

---

### 3.3 `OpenAI-Codex-API` — GPT on a ChatGPT subscription

Same models as `ChatGPT`, but billed through a ChatGPT subscription instead of
API credits. It needs **no API key**; instead it talks to a local `openai-oauth`
proxy that owns the OAuth session.

```bash
codex login       # authenticate the subscription
npx openai-oauth  # start the proxy; keep it running
```

The proxy is expected at `http://127.0.0.1:10531/v1`. AoA never starts it —
if it is not running, AoA fails immediately rather than retrying:

```
OpenAI-Codex-API: local openai-oauth proxy unreachable at http://127.0.0.1:10531/v1.
Start it (e.g. `npx openai-oauth`) and retry.
```

Driver strings mirror `ChatGPT`, effort suffix included:

```isabelle
declare [[AoA_driver = "OpenAI-Codex-API"]]                (* gpt-5.5, medium effort *)
declare [[AoA_driver = "OpenAI-Codex-API.gpt-5.5-high"]]
```

Two optional settings, only if your proxy differs from the default:

```bash
OPENAI_OAUTH_BASE_URL=http://127.0.0.1:10531/v1
OPENAI_OAUTH_API_KEY=...      # only for key-validating proxies such as auth2api
```

---

### 3.4 `DeepSeekV4` — DeepSeek V4

Needs a DeepSeek API key:

```bash
# $(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings
DEEPSEEK_API_KEY=sk-...
```

The argument is `pro` or `flash` (default `flash`), or a full model id:

```isabelle
declare [[AoA_driver = "DeepSeekV4"]]                    (* deepseek-v4-flash *)
declare [[AoA_driver = "DeepSeekV4.pro"]]                (* deepseek-v4-pro *)
declare [[AoA_driver = "DeepSeekV4.flash"]]
declare [[AoA_driver = "DeepSeekV4.deepseek-v4-pro"]]
```

Missing key gives:

```
DeepSeekV4 driver needs DEEPSEEK_API_KEY (or CHAT_API_KEY) set.
```

Optionally override the endpoint. The `/beta` suffix is required — DeepSeek's
strict tool-calling mode is only available there:

```bash
DEEPSEEK_BASE_URL=https://api.deepseek.com/beta
```

---

## 4. Further details

### 4.1 Logs

Every `by aoa` invocation writes a full record — the model's reasoning, its tool
calls, and each proof operation — under

```
$(isabelle getenv -b ISABELLE_HOME_USER)/log/AoA/<invocation-id>/
```

Change the directory, or set it to `""` to turn logging off:

```isabelle
declare [[AoA_log_dir = "/path/to/logs"]]
declare [[AoA_log_dir = ""]]                 (* no logging *)
```

### 4.2 Proof cache

AoA caches the proofs it finds, so re-processing a theory replays them instead
of paying for the model again. The cache lives next to your theory file, as
`<TheoryName>.proof-cache`. It is local build residue — delete it freely, and
do not commit it.

Reading and writing are controlled separately:

```isabelle
declare [[AoA_use_proof_cache = false]]      (* ignore cached proofs, always re-prove *)
declare [[AoA_store_proof_cache = false]]    (* do not record new proofs *)
```

Both default to `true`.

### 4.3 Memory

AoA accumulates experience across invocations and reuses it on later proofs.
This is managed automatically — nothing to configure. To stop it recording new
experience (retrieval of existing experience is unaffected):

```isabelle
declare [[AoA_enable_write_memory = false]]
```

### 4.4 Semantic retrieval

AoA finds relevant lemmas by semantic search over the library. That subsystem is
documented separately:
<https://github.com/xqyww123/Isabelle_Semantic_Embedding/blob/master/README.md>

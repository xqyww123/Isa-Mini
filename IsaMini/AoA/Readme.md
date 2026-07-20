# AoA — an AI proof agent over Isabelle/Minilang

AoA (Agent over AST) is a proof agent for Isabelle, built on Minilang. It comes as an ordinary proof method: write by aoa wherever you would write by auto or by blast, and everything from there is automatic and transparent. If the goal itself is flawed — not provable as stated — AoA will tell you that, too.

## 1. Installation

```bash
conda create -n <YOUR_ENV> -c https://conda.qiyuan.me -c conda-forge isabelle-ai
```

## 2. Quick start

Run:
```bash
conda activate <YOUR_ENV>
isabelle jedit
```
and then type:
```isabelle
theory Scratch
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

theorem sqrt2_not_rational: "sqrt 2 ∉ ℚ" by aoa

end
```

## 3. Choosing a model and providing credentials

By default, AoA drives Claude through the Claude Code CLI, so before first use you need to log in by running:
```bash
claude '/login'
```
But AoA also supports other LLMs; In short, switching models is a single declare:
```isabelle
theory Scratch
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver = "OpenAI.gpt-5.5-high"]]
theorem sqrt2_not_rational: "sqrt 2 ∉ ℚ" by aoa

end
```
which runs the proof with GPT-5.5 at high reasoning effort. The configuration option `AoA_driver` takes a string of the form `Driver` or `Driver.option`, where `Driver` is currently one of `ClaudeCode`, `ChatGPT`, `Codex-API`, or `DeepSeek`. The sections below describe each driver and the options it accepts.

### 3.1 `ClaudeCode` — Claude via the Claude Code CLI (default)

The default driver. It needs no API key — being logged into the Claude Code CLI (see above) is all it takes. Its option is a Claude model name:
```isabelle
declare [[AoA_driver = "ClaudeCode"]]                        # default: claude-opus-4-8[1m]
declare [[AoA_driver = "ClaudeCode.claude-opus-4-8[1m]"]]    # [1m] denotes the 1 million context version
declare [[AoA_driver = "ClaudeCode.claude-sonnet-4-6"]]
```

### 3.2 `OpenAI` — OpenAI API

This driver provides the GPT family of models:
```isabelle
declare [[AoA_driver = "OpenAI"]]                  # default: gpt-5.5, medium effort
declare [[AoA_driver = "OpenAI.gpt-5.5-high"]]
declare [[AoA_driver = "OpenAI.gpt-5.6-xhigh"]]
```
It requires an API key given explicitly: add the line
```
OPENAI_API_KEY=sk-...
```
to `$(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings`, then restart Isabelle.


### 3.3 `Codex-API` — GPT on a ChatGPT subscription

The `Codex-API` driver gives you the same GPT family as OpenAI, but billed through a ChatGPT subscription instead of API credits. It needs no OpenAI API key; instead, it talks to a local proxy that holds the OAuth session of your subscription. Two proxies are supported: `openai-oauth` and `auth2api`.

```isabelle
declare [[AoA_driver = "Codex-API"]]                # default: gpt-5.5, medium effort
declare [[AoA_driver = "Codex-API.gpt-5.5-high"]]
```

In addition, you must have either of the two proxies running — one is enough.

For `openai-oauth`, install it following the instructions in [https://github.com/EvanZhouDev/openai-oauth](https://github.com/EvanZhouDev/openai-oauth)
```bash
npx openai-oauth  # start the proxy; keep it running
```
With the proxy running, by aoa works in Isabelle as usual — no further configuration is needed.

For `auth2api`, install it following the instructions in [https://github.com/AmazingAng/auth2api](https://github.com/AmazingAng/auth2api)
```bash
node dist/index.js --login --provider=codex
node dist/index.js
```
Then add the lines
```
AOA_CODEX_API_BASE_URL=http://127.0.0.1:8317/v1
AOA_CODEX_API_KEY=sk-auth2api-...    # a key from auth2api's config.yaml
```
to `$(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings`, then restart Isabelle.


### 3.4 DeepSeek

The option is V4-pro or V4-flash (default V4-flash), or a full model id:
```isabelle
declare [[AoA_driver = "DeepSeek"]]                    # default: deepseek-v4-flash
declare [[AoA_driver = "DeepSeek.V4-pro"]]             # deepseek-v4-pro
declare [[AoA_driver = "DeepSeek.V4-flash"]]
```

This driver needs a DeepSeek API key: add the line(s)
```bash
DEEPSEEK_BASE_URL=...      # This can be omitted, with default: https://api.deepseek.com/beta
DEEPSEEK_API_KEY=sk-...
```
to `$(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings`, and restart Isabelle.


## 4. Further details

### 4.1 Logs

Every `by aoa` invocation writes a full record — the model's reasoning, its tool
calls, and each proof operation — under `$(isabelle getenv -b ISABELLE_HOME_USER)/log/AoA/`

Change the directory, or set it to `""` to turn logging off:
```isabelle
declare [[AoA_log_dir = "/path/to/logs"]]
declare [[AoA_log_dir = ""]]                 # disabling logging
```

### 4.2 Proof cache

AoA caches the proofs it finds, so re-processing a theory replays the caches instead
of paying for the model again. The cache lives next to your theory file, as
`<TheoryName>.proof-cache`. It records the proofs of your theory and should be
committed and distributed along with it.

The cache can be disabled with the following options — reading and writing are controlled separately:
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

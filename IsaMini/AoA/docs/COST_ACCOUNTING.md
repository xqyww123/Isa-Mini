# Token Cost Accounting (AoA)

How AoA records token usage and computes dollar cost across every LLM driver.
This restates the project-wide convention locally; see "Consistency" at the end.

## 1. Canonical token partition

Every driver reports four cumulative counters on the session:

- `total_input_tokens` — **uncached input only**
- `total_cache_creation_input_tokens` — tokens written to cache
- `total_cache_read_input_tokens` — tokens served from cache
- `total_output_tokens` — generated output

The three prompt-side counters are **mutually exclusive partitions**:

    total_prompt = input + cache_creation + cache_read

**Invariant:** `total_input_tokens` is always uncached. Anything that records
tokens does so by building a `language_model_driver.Usage` via a factory
(below) and calling `LMDriver._accumulate_usage`, so this holds by construction.

## 2. Provider conventions

Providers disagree on whether their reported prompt count includes cache, so
each is normalized once at ingestion:

| Provider | Reported prompt count | Cache creation reported? | Normalization |
|---|---|---|---|
| Anthropic | already **excludes** cache | yes | pass through (`from_uncached`) |
| OpenAI | **includes** cached and cache-written | Responses: `input_tokens_details.cache_write_tokens` (read since 2026-09-25); Chat Completions and Codex CLI: no | subtract both (`from_inclusive`) |
| Gemini | **includes** cached | no (always 0) | subtract cached (`from_inclusive`) |

Sources:
- OpenAI — `usage.input_tokens` total incl. cached; cached in `input_tokens_details.cached_tokens`: https://platform.openai.com/docs/api-reference/responses
- OpenAI cache writes — that `input_tokens` includes them rests on the pricing page's Cache writes tooltip, "Input tokens are either Input, Cached Input, or Cache Write and writes are not an additive fee" (https://developers.openai.com/api/docs/pricing, read 2026-09-25). `cache_write_tokens` is not in the openai SDK's typed `InputTokensDetails` (2.33.0); it was observed on the codex backend on 2026-09-25 with value 0 — neither a non-zero value nor the inclusion has been observed yet.
- Gemini — `usageMetadata.promptTokenCount` includes `cachedContentTokenCount`: https://ai.google.dev/api/generate-content
- Anthropic — `input_tokens` excludes cache; cache in `cache_read_input_tokens` / `cache_creation_input_tokens`: https://docs.anthropic.com/en/docs/build-with-claude/prompt-caching

## 3. Implementation map

- `Usage.from_uncached(...)` / `Usage.from_inclusive(...)` — the only blessed
  ways to build a `Usage` from a provider's report; encode the per-provider
  convention.
- `Usage.cost(rates)` — the §4 partition sum at one price tier; `Usage()` and
  `+` build tallies and keep the invariant.
- `LMDriver._accumulate_usage(usage)` — the single funnel into the counters;
  touches token counters only, never `total_cost_usd`.
- Where each driver normalizes:
  - `driver_anthropic.py` (`AnthropicProvider.chat`) → `from_uncached`
  - `driver_openai_api.py` (`_responses_usage`; `OpenAIChatProvider.chat`) → `from_inclusive`
  - `driver_gemini.py` (`GeminiProvider.chat`) → `from_inclusive`
  - `driver_codex.py` (`_record_codex_usage`) → `from_inclusive`
  - `driver_claude_code.py` (`_accumulate_cost`) → `from_uncached`
- **ClaudeCode's cost source** (`_sdk_loop` → `_accumulate_cost`) is the
  **remote-reported** `message.total_cost_usd` (authoritative; the price
  table is not used) — but that field is a *running total within one CLI
  session*, not a per-turn amount, so `_accumulate_cost` adds the per-session
  increment over the highest value seen (`_cost_by_session`), never the raw
  value.

## 4. Pricing & cost formula

`PRICING` (in `language_model_driver.py`) maps model → per-token USD rates
(`input`, `cached` = cache-read rate, optional `cache_write`, `output`).
`pricing_for(model, default)` looks up a model, falling back to a family
flagship (`gpt-4.1` / `claude-opus-4-6` / `gemini-2.5-pro`). Each driver
exposes its rate dict via `_pricing()`.

`LMDriver._compute_cost()` is a partition sum — **no subtraction**, because
`input` is already uncached:

    cost = input·input_rate
         + cache_creation·cache_write   (falls back to input_rate if absent)
         + cache_read·cached
         + output·output_rate

Claude cache pricing uses the **5-minute ephemeral TTL**: `cache_write` =
1.25× input, `cached` (read) = 0.1× input.

**Long context (OpenAI).** The OpenAI pricing page's Short / Long context
columns are "≤272K input tokens" / ">272K input tokens" (its column tooltips),
input tokens being input, cached input or cache write together; every row with
a long-context price lists 2× input / cached / cache_write and 1.5× output. AoA
reads this as: a request whose prompt exceeds the threshold is billed at the
long rates as a whole, output included. Such a model's `PRICING` row carries a
`long` sub-dict (the same keys plus `threshold`).

Two-tier billing needs each `Usage` to describe exactly one model request.
Every API driver meets this, because `APIDriver`'s loop records usage once per
response. The Codex CLI and Claude Code drivers do not: they report per-turn
sums, so they stay on the flat formula above. As a scope decision, only
`APIDriver_OpenAI` (hence `Codex-API`) bills in two tiers, and the other API
drivers bill flat. For their own models this changes nothing, because their
rows have no `long` tier. The exception is `Chat` running `gpt-5.5-pro`,
`gpt-5.5` or `gpt-5.4`: its 384K window lets requests above 272K through
before compaction starts (at 80%, about 307K), and those requests are billed
at the short rates. The driver keeps two disjoint tallies, `short_context_usage`
and `long_context_usage`, each a `Usage`; `_accumulate_usage` adds every call
to exactly one of them (a call is long when its `prompt_tokens` exceed the
model's `long.threshold`; a model without a `long` tier is always short) and
logs the USAGE record with `long_context: true/false`, meaning "billed at the
long rates". `_compute_cost` is then `short.cost(rates) + long.cost(long rates)`
— the same partition sum applied twice, with no subtraction. The four Session
totals (the exported DB fields) are their sum and are unchanged.

## 5. DB compatibility — pre-fix warning (2026-06-04)

Before **2026-06-04**, AoA recorded OpenAI/Gemini `input_tokens` as the
cache-*inclusive* total. Such rows are **not migratable** (the cached share
cannot be recovered after the fact) and, summed as `input + cache_read +
cache_creation`, double-count the cached portion. Re-run those evaluations
with current code; do not mix pre/post-2026-06-04 OpenAI/Gemini rows in one
DB. ClaudeCode/Anthropic rows are unaffected (already uncached).

## 6. Consistency

This document restates the project-wide token-accounting convention. The other
statement of it lives in the evaluation harness; the two must stay consistent.

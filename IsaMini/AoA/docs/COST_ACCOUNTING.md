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
| OpenAI | **includes** cached | no (always 0) | subtract cached (`from_inclusive`) |
| Gemini | **includes** cached | no (always 0) | subtract cached (`from_inclusive`) |

Sources:
- OpenAI — `usage.input_tokens` total incl. cached; cached in `input_tokens_details.cached_tokens`: https://platform.openai.com/docs/api-reference/responses
- Gemini — `usageMetadata.promptTokenCount` includes `cachedContentTokenCount`: https://ai.google.dev/api/generate-content
- Anthropic — `input_tokens` excludes cache; cache in `cache_read_input_tokens` / `cache_creation_input_tokens`: https://docs.anthropic.com/en/docs/build-with-claude/prompt-caching

## 3. Implementation map

- `Usage.from_uncached(...)` / `Usage.from_inclusive(...)` — the only blessed
  ways to build a `Usage`; encode the per-provider convention.
- `LMDriver._accumulate_usage(usage)` — the single funnel into the counters;
  touches token counters only, never `total_cost_usd`.
- Where each driver normalizes:
  - `driver_anthropic.py` (`AnthropicProvider.chat`) → `from_uncached`
  - `driver_api.py` (OpenAI responses + chat-completions) → `from_inclusive`
  - `driver_gemini.py` (`GeminiProvider.chat`) → `from_inclusive`
  - `driver_openai.py` (`_ProverHooks.on_llm_end`) → `from_inclusive`
  - `driver_codex.py` (`_record_codex_usage`) → `from_inclusive`
  - `driver_claude_code.py` (`_accumulate_cost`, `_read_cost_from_session_log`) → `from_uncached`
- **ClaudeCode has two cost sources.** Primary in-process SDK mode
  (`_sdk_loop` → `_accumulate_cost`) takes the **remote-reported**
  `message.total_cost_usd` directly (authoritative; the price table is not
  used). The standalone external-CLI mode (`_run_standalone` →
  `_read_cost_from_session_log`) reconstructs cost from logged tokens via the
  shared formula below.

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

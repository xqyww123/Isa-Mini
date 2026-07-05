# Experience Memory — Design & Implementation Spec

> Status: **IMPLEMENTED & VERIFIED.** All functional decisions and agent-facing
> wording are user-approved and shipped. ML (`Universal_Key.ML`, `context.ML`,
> `agent_server.ML`) compiles; the relaxed unifier + antichain have 33 isabelle-mcp
> unit tests; all Python compiles; and the whole write→retrieve→render loop passes
> an end-to-end golden test (`@model_test("ExperienceMemory")`,
> `Tests/Test_ExperienceMemory.thy`, `Tests/ExperienceMemory.yml`) against a live
> REPL with real embedding. This doc is the as-built spec; §11 lists the touched
> files.

## 0. Goal

The AoA agent can **record reusable proof experience** — a proof strategy for a
*general class of goals* — via a new `write_memory` tool, and **retrieve it in
future proofs** via the existing `query` tool (new `kinds: ["experience"]`),
fully integrated into the `Semantic_Embedding` stack (same `EntityKind` /
`Semantic_DB.Record` / vector store; no new record/vector data structure). RAG =
semantic embedding (cosine) + structural pattern matching (a relevance boost).

---

## 1. Data model

### 1.1 `EntityKind` (`Isabelle_RPC/Isabelle_RPC_Host/universal_key.py`)
- Add `EntityKind.EXPERIENCE = 8`; `_ENTITY_LABELS[EXPERIENCE] = "experience"`;
  reverse in `_LABEL_TO_ENTITY`.
- **Not** in `EntityKind.ALL` (experiences are not enumerated from the Isabelle
  context; they have their own availability path).

### 1.2 `Record` mapping (`Semantic_Embedding/.../semantics.py` `_Semantic_DB.Record`)
Add ONE trailing field `experience: str | None = None`. `_encode` appends it;
`_decode` pads to 7 fields (trailing-field addition is naturally backward
compatible; version compat not required). A prominent comment on `Record` MUST
document the EXPERIENCE-specific field meanings:

| Record field | meaning when `kind == EXPERIENCE` |
|---|---|
| `kind` | `EXPERIENCE` |
| `name` | agent-provided `name` (short, stable, descriptive id) |
| `expr` | the `goal_patterns` joined (implementation delimiter, e.g. length-prefixed / JSON) |
| `interpretation` | `goal_description` (the "WHEN to use" NL; this is what is embedded) |
| `theory_constituents` | the **minimal antichain** of constituent theories `[(long_name, 16B hash)]` — drives availability |
| `experience` (new) | the how-to-prove payload (NL); **NOT embedded** |

### 1.3 Universal key
32 bytes, same layout as thm/rule keys:
```
<16B  XOR of minimal-antichain constituent theory hashes>  <1B tag=8>  <15B hash>
```
- `hash = xxhash128(name ‖ normalize(goal_patterns) ‖ goal_description ‖ experience)[:15]`,
  fixed seed. `normalize` = whitespace collapse only.
- `destruct_key` (`universal_key.py:141`): add `EXPERIENCE` to the **raw-bytes**
  payload branch (no `decode('utf-8')`).
- `is_thm_rule_key` (tag-based) returns False for tag 8 — this is handled by §10.

---

## 2. Key computation — split ML / Python (REVISED, user-approved)

**Division of labour** (revised from "ML computes key"): ML never sees
`name`/`goal_description`/`experience` — only the `goal_patterns` reach it, since
only they need theory resolution. And ML has no native xxhash128 (the existing
`theory_hash.ML` xxhash is itself an RPC call *into* Python). So:

**ML callback `Experience.constituents`** (`context.ML`, registered in
`agent_server.ML`'s AoA callback list):
- Input `(context, goal_patterns : string list)`.
- `parse_patterns` each pattern (pattern mode → schematic Vars; free vars
  generalized).
- Union the constituent theories of the patterns' constants+type constructors
  via the now-exposed `Universal_Key.compute_constituents` (per term), dedup by
  theory long name (`Symtab`).
- **Reduce to the maximal antichain** under the import order (`Theory.subthy`,
  resolving each long name via `try Thy_Info.get_theory`; unresolvable → keep):
  drop an ancestor theory when a descendant that imports it is also present.
  Sound because the loaded set is import-closed: `minimal ⊆ loaded ⇔ full ⊆ loaded`.
- Returns just `constituents : [(thy_long_name, 16B hash)]`
  (ret_schema `packList (packPair (packString, packBytes))`). **No hashing, no
  XOR, no key in ML.**

**Python `write_memory`** assembles the whole key (it holds all the strings and
has native xxhash + `xor_theory_prefix`):
- `prefix = xor_theory_prefix([h for _,h in constituents])` (already mirrors
  `compute_constituents`' XOR/WIP convention — kept in sync).
- `hash15 = xxhash128(normalize(name ‖ goal_patterns ‖ goal_description ‖ experience))[:15]`.
- `key = prefix ‖ bytes([EntityKind.EXPERIENCE]) ‖ hash15`.
- Stores the `Record` (with `theory_constituents = constituents`), updates the
  inverted index, embeds the document.

---

## 3. Storage, availability, inverted index (Python) — Q1, Q2

### 3.1 Records
Experience `Record`s live in the existing `semantics.lmdb`, keyed by the 32B key.
Vectors live in the existing `vector_<model>.lmdb` (same store as entities).

### 3.2 Inverted index (Q2 = **separate LMDB**)
`theory_hash (16B) → [experience uk]`, in its **own** small LMDB file (e.g.
`experience_index.lmdb`) — NOT co-located in `semantics.lmdb` (avoids all
whole-DB cursor-scan collisions: `clean_wip`, `semantics_manage` list/remove).
Maintained incrementally on `write_memory`: insert appends the uk to each
minimal-constituent bucket; overwrite removes the old uk from every bucket first.

### 3.3 Availability
Given loaded theory hash set `S`: `candidates = ⋃_{t∈S} inverted[t]` (deduped) →
linear filter `theory_constituents ⊆ S` → `[(uk, pattern_strings)]`. One pass per
`by aoa`; the loaded set is fixed for the whole run (Isabelle theory/proof
separation forbids mid-proof imports), so no mid-run refresh.

### 3.4 Q1 = **Python-driven, pattern strings passed per experience-query**
AoA is Python-driven (`IsaMini_AoA` handler in control; ML is the callee). At AoA
init, Python asks ML for the loaded theory hashes (cheap callback), computes the
available set via §3.3. On each **experience-query**, Python passes the available
`(uk, pattern_strings)` as arguments to the `Context.experiences` ML callback;
ML parses (memoized by pattern string) and unifies. **Stateless ML — no prep
cache, no separate ML-side load step.**

---

## 4. Matching (ML, `context.ML`)

### 4.1 `_relaxed` rename
Rename `*_transparent → *_relaxed` (`first_order_match_relaxed`, `match_relaxed`,
`matches_relaxed`, `matches_subterm_relaxed`) + call sites. Definition comment:
**relaxed = ignores types (type-agnostic) + coercion-transparent (skips the
`coercion_ignores` unary wrappers: `of_nat`/`of_int`/`of_real`/…).** Kernel logic
unchanged. (This is a pure local rename; keep `is_thm_rule_key`-unrelated.)

### 4.2 Two orthogonal flags (combinator layer, kernel untouched)
Add to `matches_subterm_relaxed` / the closure builder:
- `mode ∈ {match, unify}` — `match` = existing one-directional `matches_relaxed`;
  `unify` = new `unify_relaxed` (§4.3).
- `scope ∈ {whole, subterm}` — whether to walk subterms.

### 4.3 `unify_relaxed` = **modified copy of stdlib `Pattern.unify`** (approved)
Base it on Isabelle stdlib `Pattern.unify` (`src/Pure/pattern.ML`) — symmetric to
how `match_relaxed` descends from `Pattern.match`. Apply the same two
modifications: (a) **remove type unification** → type-agnostic; (b) **skip the
`coercion_ignores` unary wrappers** → coercion-transparent. (Removing
type-unification is slightly more delicate than removing `typ_match` in the
matcher, but is a bounded modification of a reliable core.)
- `Pattern.unify` is the higher-order **pattern (Miller)** unifier; it raises the
  stdlib `Pattern` exception on non-Miller problems (applied/repeated schematics
  like `?P (?f ?x)`, `?R ?x ?x`). **On `raise Pattern`, fall back to the
  bidirectional `first_order_match_relaxed`** — exactly mirroring `match_relaxed`'s
  own HO→FO fallback. This is the resolution of review concern #1 (do NOT
  `can`-wrap all exceptions to false, which would conflate "not a pattern" with
  "not unifiable"). `Pattern.Unif` / `Fail` → false (genuinely no unifier).
- Do NOT use `Unify.unifiers` (full Huet HO unifier): too complex to modify
  reliably, expensive (search), returns flex-flex residuals.
- **After any `.ML` edit, the REPL server must be restarted to load it.**

### 4.4 Bidirectional subterm + hit_rate
`hit(q, e)` ⟺ `q` `unify_relaxed`s a **subterm of** `e`  OR  `e` `unify_relaxed`s
a **subterm of** `q`. For a query pattern set `Q`, experience pattern set `E`:
`hit_rate = |{ q ∈ Q : ∃ e ∈ E. hit(q, e) }| / |Q|`.

---

## 5. `Context.experiences` callback + relevance (ML)

- Over the available experiences' parsed patterns (passed per §3.4), compute
  `hit_rate` per experience. **Gate `hit_rate > 0` applies ONLY when the query
  supplies ≥1 term pattern** (decision C). If the query supplies **no** term
  patterns (decision A), there is no pattern gate and no hit_rate — experiences
  are ranked by pure semantic similarity, boost disabled (like constant/lemma).
- Return `(uk, hit_rate)` for survivors. New `ret_schema_experience` carrying a
  `float`.

---

## 6. Relevance boost (general mechanism, all kinds)

The per-entry relevance boost is a **general, kind-agnostic** channel (generalizes
the existing `is_local → default_score` precedent):
- Every candidate carries a per-entry `hit_rate ∈ [0,1]`. **Implementation:
  default `hit_rate = 1` in Python for kinds whose callback doesn't return one**
  (constant/type/theorem/rules are hard-filtered → survivors have hit_rate 1 →
  boost neutral → **no behavior change**). Experiences return a real fraction.
  **Theorem bundles are the intended future beneficiary** (today a boolean
  any-member gate; the plumbing lets them return a fractional hit_rate later).
- Boost formula (β = 0.25):
  `final = score + (1 − score) · β · hit_rate` — convex combination of `score`
  and 1, weight `β·hit_rate ∈ [0,1]` ⇒ `final ∈ [score, 1] ⊆ [−1,1]`, no clamp.
  Linear (no nonlinearity `g`).
- **Single-pattern-off**: if the query has exactly **one** term pattern, skip the
  boost (`final = score`) — with one pattern every survivor has hit_rate 1, so the
  boost is uniform. **No-pattern (decision A)**: boost disabled entirely.
- **Stage-1 only (review concern #2 resolution)**: the boost is applied to the
  Stage-1 bi-encoder cosine. It is the final ranking when no reranker; when a
  reranker is configured, the boosted Stage-1 order **selects the top-N pool fed to
  the cross-encoder**, and the **reranker's output is returned untouched** (no
  boost/normalization applied to reranker scores — the learned model is
  authoritative for Stage-2).
- **Q5 = numeric mixing** works in both cases: no reranker → all candidates on the
  boosted-cosine scale; reranker on → all candidates (entities + experiences) go
  through the **same** cross-encoder → one scale.

---

## 7. Retrieval integration (Python)

### 7.1 kinds
`query` schema `kinds` enum gains `"experience"`. An agent may select it alone or
mixed with other kinds in one sub-query (Q5 numeric mixing).

### 7.2 Two Stage-1 passes (different query embeds), merged
- **Entities**: `entities_of` enumeration → `topk` with the `{kinds}` task
  sentence embed → `(uk, cosine)`, hit_rate defaults to 1.
- **Experiences**: candidates from §3.4 (availability + `Context.experiences`
  hit_rate) → embed the query with the **experience task sentence** (§8.2,
  `task_override`) → `topk` over experience vectors → `(uk, cosine, hit_rate)`.
- `topk` accepts a vector query (skips its own embed), so the experience pass
  embeds the query itself with `task_override` and hands `topk` the vector.
- Merge both candidate lists; apply §6 boost.

### 7.3 Stage-2 (only if reranker configured)
Feed the boosted-Stage-1 top-N (entities + experiences) to the cross-encoder
(`raw query text` × each `doc_text`; experience `doc_text` = its
`goal_description`); return the reranker order untouched (§6). Else sort by boosted
score. **Dedup experiences by `uk`** (not `name`) so same-name experiences don't
collide.

### 7.4 Rendering (LOCKED — `_format_fetched_entity` in `retrieval.py`)
An experience hit renders (via `print_paragraph`, so each field is inline when
one line, or a `|` block scalar indented one level when multi-paragraph):
```
- experience `⟨name⟩`:
    When to use: ⟨goal_description⟩
    Experience: ⟨full experience payload, not truncated⟩
```
`goal_patterns` are not shown. Labels: "When to use:" / "Experience:".

---

## 8. Embedding

### 8.1 Document text (embedded at write time; content NOT embedded)
```
This is an experience that aims to help prove goals of the following forms:
- {goal_pattern_1}
- {goal_pattern_2}
The experience should be used in the following situation:
{goal_description}
```
Embed via a dedicated path (NOT `_embed_keys`/`with_pretty`):
`Vector_Store.embed([(uk, document_text)])`. The `experience` payload is NOT part
of the embedded text (keeps the WHEN-to-use signal clean; payload-only edits need
no re-embed).

### 8.2 Query task sentence (Stage-1 experience embed)
Fills the `{task}` slot of the Qwen query template (`Instruct: {task}\nQuery: {text}`):
```
Given a proof situation, retrieve experiences and proof strategies that help prove the goal
```
Add `experience_task_description` to `embedding_config`; add a `task_override`
param to `Embedding_Provider._apply_template` / `embed`; the experience Stage-1
pass passes it. Qwen wrappers and the entity task sentence are unchanged. `{kinds}`
is not used for experiences.

---

## 9. `write_memory` tool

### 9.1 Schema (`tools/cc_write_memory.jsonc`) — all texts LOCKED
```jsonc
{
  "type": "object",
  "properties": {
    "name": {
      "type": "string",
      "description": "A short, stable, descriptive identifier for this experience; reuse the same name to update it."
    },
    "goal_patterns": {
      "type": "array",
      "minItems": 1,
      "items": {
        "type": "string",
        "description": "An Isabelle term pattern. Use ?x for a named wildcard and _ for an anonymous one. Any literal number MUST be annotated with its type, e.g. (0::real), (2::nat). Example: `DERIV ?f ?x :> ?D`."
      },
      "description": "Non-empty list of Isabelle term patterns characterizing the proof goals this experience applies to. Be comprehensive — include enough patterns to cover the goal shapes it handles, not just one."
    },
    "goal_description": {
      "type": "string",
      "description": "English description of WHEN to use this experience. E.g. \"Establishing the derivative of a function.\""
    },
    "experience": {
      "type": "string",
      "description": "How to complete the proof — the strategy and any useful specifics, e.g. which proof operations, lemmas, or named theorem bundles to use, and whatever else helps. For instance: \"Use `Obvious with facts derivative_eq_intros` for derivative goals; it also discharges a pre-simplified derivative value.\""
    }
  },
  "required": ["name", "goal_patterns", "goal_description", "experience"],
  "additionalProperties": false
}
```

### 9.2 Tool description (LOCKED)
```
Save an experience or a proof strategy so future proofs can reuse it. Note: what you save must generalize to a specific class of problems — not a single one-off goal.
```

### 9.3 Tool logic (`mcp_http_server.py`) — overwrite via Runtime map (REVISED)
`TOOL_WRITE_MEMORY = "write_memory"`, registered in `_TOOL_SCHEMAS` (mutation
annotation) and in `ALL_PROOF_TOOLS` (so interaction forks are blocked by
`_check_tool_permission`; planner + workers can call it — Q3).

**Key is content-addressed (§1.3 unchanged):**
`key = xor_prefix(constituents) ‖ tag8 ‖ xxhash128(normalize(name ‖ goal_patterns
‖ goal_description ‖ experience))[:15]`.

**Overwrite is via a Runtime-level map, NOT a DB scan (user-approved):** the AoA
Runtime holds `created_memories: dict[name → uk]`, shared across the whole AoA
invocation (planner + all workers). Flow:
1. Normalize args; `constituents = await conn.callback("Experience.constituents",
   (ctxt, goal_patterns))`.
2. `prefix = xor_theory_prefix([h for _,h in constituents])`;
   `hash15 = xxhash128(normalize(name‖patterns‖desc‖experience))[:15]`;
   `key = prefix ‖ bytes([EntityKind.EXPERIENCE]) ‖ hash15`.
3. **If `name` in `created_memories`** (created earlier THIS run) → update: delete
   the recorded old uk from `semantics.lmdb` + vector store + every inverted-index
   bucket (skip if old uk == new key).
4. Write `Record(EXPERIENCE, name, expr=join(patterns), interpretation=desc,
   theory_constituents=constituents, experience=payload)`; add uk to the inverted
   index; embed the document text (§8.1); set `created_memories[name] = key`.
5. **If `name` NOT in the map** → fresh create (never scans the DB, never touches a
   pre-existing / prior-session memory). A cross-session same-name write with
   different content coexists; identical content is absorbed idempotently by the
   content-addressed key (same uk).

"Reuse the same name to update it" therefore holds WITHIN an AoA run; pre-existing
memories from other runs are immutable to this run.

### 9.4 Access (Q3)
Planner + workers (like other mutation tools); not interaction forks.

### 9.5 Agent introduction (LOCKED, implemented in `model.py` `system_prompt`)
Three additions to the system prompt (planner + worker; interaction forks get only
the `query` rewrite):
- **`## Tools` — rewritten `query` line** (all roles):
  "Search for theorems, constants, types, rules, and saved experiences (proof
  strategies); also help you understand unfamiliar terms".
- **`## Tools` — new `write_memory` line** (in the `is_major or is_worker` block,
  beside subagent): "Save a reusable proof experience or a strategy for a general
  class of goals, so future proofs can retrieve it using the `query` tool."
- **body prose reminder** (planner: after the breadth-first list; worker: after the
  lemma guidance): "You can also `query` with `kinds: [\"experience\"]` to retrieve
  saved proof experiences (strategies) relevant to your goal."

---

## 10. XOR-migration fix (`is_xor_prefixed_key`) — review concern #3

Two concepts that coincided before experiences existed now diverge:
- `is_thm_rule_key` — narrow "is a theorem/rule" (sibling / cross-kind dedup /
  legacy purge).
- **`is_xor_prefixed_key`** (NEW) — broad "has an XOR pseudo-theory prefix + a
  constituent list" (migration / theory-membership / locability).

Add to `universal_key.py`:
```python
_XOR_PREFIXED_TAG_BYTES = _THM_RULE_TAG_BYTES | frozenset({int(EntityKind.EXPERIENCE)})
def is_xor_prefixed_key(key):  # len==32 and key[16] in _XOR_PREFIXED_TAG_BYTES
    ...
```
Keep `is_thm_rule_key` unchanged. **Switch these call sites to
`is_xor_prefixed_key`** (all XOR-migration / theory-membership / locability):
`semantics.py:313` (`_copy_prefix`), `:333` (`keys_belonging_to`), `:354`
(`_migrate_thm_records` — consider renaming `_migrate_constituent_records`),
`:913` (`_auto_embed` missing-theory scan); `semantics_manage.py:169, 241, 260,
302, 320`. **Keep `is_thm_rule_key`** at `migrate_xor_thm_keys.py:39` (legacy
pre-XOR purge must not sweep experiences). Cross-kind/sibling logic in `context.py`
uses `RULE_ONLY_TAG_BYTES`/`theorem_sibling_key` (untouched — experiences have no
sibling). Also: **refresh the (separate) inverted index** for experiences rekeyed
during theory migration (`_try_migrate` / the constituent-migration path).
Safe: experience records always carry `theory_constituents` (no false
`pre-XOR legacy` raise); the XOR recompute preserves `key[16:]` (tag + 15B hash).

---

## 11. Implementation phases (file anchors)

1. `universal_key.py` — `EntityKind.EXPERIENCE=8`, labels, `destruct_key` raw
   branch, `is_xor_prefixed_key`, experience-key helper.
2. `semantics.py` — `Record` 7th field + comment; encode/decode; experience embed
   path; §6 boost + §7.2/7.3 two-pass merge in ranking; availability helpers;
   `is_xor_prefixed_key` re-points (§10); inverted-index refresh on migration.
3. `experience_index.lmdb` handling (Python) — inverted index open/update/query
   (separate LMDB).
4. `context.ML` — `_relaxed` rename; `unify_relaxed` (modified `Pattern.unify` +
   bidirectional FO fallback) + two-flag `hit_relaxed`; callbacks
   `Experience.constituents` (write-side antichain), `Context.experiences`
   (retrieval hit_rate, ret `packList(packPair(pack_uk, packReal))`), and
   `Context.loaded_theory_hashes` (availability). `Universal_Key.ML` exposes
   `compute_constituents`.
5. `agent_server.ML` — register the three callbacks in the AoA callback list.
6. `semantics.py` — `_experience_hits` (loaded_theory_hashes + inverted-index
   availability + `Context.experiences`); `lookup` two-track merge + §6 boost.
   (`entities_of` self-skips EXPERIENCE — no per-kind branch needed.)
7. `mcp_http_server.py` — `write_memory` tool + logic + register; `Runtime`
   gained `created_memories`; `Semantic_DB.delete` / `Vector_Store.delete`.
8. `tools/cc_write_memory.jsonc` — schema (§9.1).
9. `embedding_config` — `experience_task_description`; `_apply_template`/`embed`
   `task_override`.
10. `model.py` / `retrieval.py` — kinds enum; `RetrievedEntity.experience` field +
    resolution loop + `_format_fetched_entity` render (§7.4); pattern-only branch
    hit_rate merge.
11. `semantics_manage.py` — `is_xor_prefixed_key` re-points (§10).
12. System prompt (`model.py`) — `write_memory` tool line, `query` line rewrite,
    body reminder (§9.5).

`semantics_manage.py` / `migrate_xor_thm_keys.py` are in
`Semantic_Embedding/`; the ML files in `Isa-Mini/Agent/` and
`Isabelle_RPC/Tools/`; the rest in `Isa-Mini/IsaMini/AoA/`.

---

## 12. Tests (implemented)
- **ML unit tests (isabelle-mcp)** — 24 for `unify_relaxed` (type-agnostic,
  coercion-transparent incl. nested/both-sides/in-arg, occurs-check, HO Miller /
  projection / flexflex / eta, non-Miller FO fallback, match-mode asymmetry,
  subterm-in-binder, subterm flag) + 9 for the `Context.subthy` antichain
  reduction (ancestor-drop, chain-collapse, current-theory-wins, unresolvable-kept,
  incomparable-both-kept, empty).
- **End-to-end golden** — `@model_test("ExperienceMemory")` in `test.py`
  (`Tests/Test_ExperienceMemory.thy`, golden `Tests/ExperienceMemory.yml`): drives
  `write_memory` (a derivative strategy) then a `kinds=["experience"]` retrieval
  against a live REPL with real embedding, checking the render; cleans up the
  written record so the shared DB stays empty and re-runs are deterministic.
  Passes.

---

## 13. Decision ledger (all user-approved)
EntityKind 8; 32B key (XOR antichain + tag + 15B xxhash128, hash over
name‖patterns‖desc‖experience, whitespace-normalize); `destruct_key` raw branch;
Record +`experience` field; **overwrite via Runtime `created_memories` (name→uk),
same-run only** (content-addressed key makes cross-run identical writes idempotent);
separate LMDB inverted index (Q2); Python-driven availability via
`Context.loaded_theory_hashes` + inverted index, per-query pattern pass to
`Context.experiences` (Q1);
`_relaxed` rename; two flags; `unify_relaxed` = modified `Pattern.unify` +
bidirectional FO fallback (#1); type-agnostic + coercion-transparent unify (B);
bidirectional subterm; hit_rate = matched-query-pattern fraction; **A**:
no-pattern query → pure semantic, boost/gate disabled; **C**: gate only with ≥1
pattern; general hit_rate channel (default 1; experiences fractional; bundles
future); convex boost β=0.25, single-pattern-off, linear; Stage-1-only boost,
reranker output untouched, pool selected by Stage-1 order (#2); Q5 numeric mixing;
document template (patterns-first, content not embedded); query task sentence;
`is_xor_prefixed_key` re-point (#3); write_memory access planner+workers (Q3);
rendering shows name+description+full payload via `print_paragraph` block scalars,
labels "When to use:" / "Experience:" (Q4/§7.4); system prompt A+B1+V1 (§9.5).
**All items shipped and verified (see status header).**

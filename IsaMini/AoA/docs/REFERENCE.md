# AoA Retrieval — Behavioral Reference & Known Limitations

This document records observable **behavioral contracts and limitations** of
AoA's semantic retrieval (the `query` tool and the ML entity-enumeration that
backs it). It complements `DEVELOP.md` (which covers design and rationale): use
this file when you need to know *what the system guarantees and what it does
not* at the boundary of the retrieval layer.

---

## 1. Dynamic facts that appear *during* a proof are not retrievable in that same `by aoa`

### Statement

During a single `by aoa` tactic invocation, the `query` tool retrieves a
**fixed snapshot** of the available facts that is taken once, when the tactic
starts. Consequently:

- **Members of a dynamic collection** (a `named_theorems` bundle, or a raw
  `add_thms_dynamic` collection such as `Deriv.derivative_eq_intros`) that
  **newly appear after the tactic started** — e.g. because a proof step added a
  lemma to the bundle (`have foo[derivative_intros]: …`, or any command that
  grows the bundle) — are **not** returned by `query` for the remainder of that
  tactic. They become retrievable only on the next `by aoa` run (or after a
  fresh collect/embedding pass).

- This is **specific to dynamic-collection membership**. It is distinct from the
  general case of the agent's own `have`/`obtain` lemmas: ordinary *static*
  facts the agent proves mid-tactic *are* picked up incrementally (see
  "Mechanism" below), because they are enumerated through the static path. Only
  the *dynamic-collection* delta is missed.

### What is NOT affected

- **Members that already existed at tactic start** are fully retrievable and
  behave normally.
- **Whole-collection references are always correct.** A retrieved member is
  cited as `coll(i)` (its position in the collection's *current* content) or via
  the whole bundle `coll`; either reference is resolved by Isabelle against the
  collection's **live** content at use time, so it never points at a stale or
  wrong theorem even if the collection has since changed. The limitation is one
  of *recall* (a brand-new member is not surfaced as a candidate), never of
  *correctness* (no member is ever mis-cited).

### Mechanism (why)

The `Context.theorems` callback that serves `query` is built **once** per
tactic, in the preparation phase (`Semantic_Store.make_entity_callbacks`, called
from `agent_server.ML` when `by aoa` starts). At that point it:

1. snapshots the static facts (`Thm_Cache` + the current `Facts.dest_static`
   delta), and
2. enumerates the members of every visible non-infra dynamic collection
   (`process_dynamic_facts_into_cache`) **once**, baking them into the snapshot.

Per query, the callback then serves from that snapshot, plus an *uncached* path
that supplements facts added since the snapshot. The uncached path uses
`Facts.dest_static`, which by construction returns **only static facts** — it
never re-evaluates dynamic collections. Re-enumerating dynamic collections on
every query was deliberately rejected: it would re-synthesize every computed
bundle (e.g. re-running `derivative_eq_intros`' `eq_rule OF …` over its base
rules) on each `query`, which is the per-query cost the prep-once snapshot
exists to avoid.

### Example

```
lemma "…"
by (aoa)        ──▶ tactic starts; snapshot taken here.
  • step: have aux_rule[derivative_intros]: "…"   (* grows derivative_eq_intros *)
  • step: query "a derivative rule for my new function"
            └─ the freshly added member is NOT among the candidates this tactic;
               members of derivative_eq_intros present at snapshot time ARE.
```

### Workaround

If a proof depends on retrieving a fact it has just introduced into a dynamic
bundle, do not rely on `query` for it within the same tactic — reference it
directly (the agent already holds its name), or state it as an explicit `Have`
node rather than discovering it through search.

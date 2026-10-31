"""The link layer's display owner function at AoA's record readers
(Semantic_Embedding/ai-artifacts/LINK_LAYER_PLAN.md §4.2, §7 P2): the query
tool's core (`_query_entity_core`, also behind the IsaMini.query_by_name RPC)
and `semantic_knn_counted`'s exact-name and pattern-only branches show a linked
local fact by its display record and every other key by its stored record, as
a direct read gives it, and no rendered text carries the display record's
entities block (D50); the pattern-only branch hides the template of a linked
local fact, and a constant's lookup never fetches the links (B6, D61).  An isolated SEMANTIC_DB_DIR and a fake connection; no
Isabelle, no LLM.
Run with  python -m pytest contrib/Isa-Mini/IsaMini/AoA/test_link_display_owner.py
"""
import asyncio
import os
from types import SimpleNamespace

import pytest

from Isabelle_RPC_Host.universal_key import EntityKind


def key(n: int) -> bytes:
    return bytes([0x40 + n] + [n] * 15) + bytes([int(EntityKind.THEOREM)]) + bytes([n] * 15)


TEMPLATE, LOCAL, GLOBAL = key(1), key(11), key(6)
LE = bytes([0x20] * 16) + bytes([int(EntityKind.CONSTANT)]) + b"Foo.le"
WIRE = [(LOCAL, (TEMPLATE, "x \\<le> y \\<Longrightarrow> y \\<le> x \\<Longrightarrow> x = y",
                 "Orderings.ordering", ("antisym", 0), [(1, "less_eq", "le")], [], [("le", LE)]))]
COPY = ("This entry is the template `antisym` of the locale `Orderings.ordering` with its parameters "
        "renamed: less_eq is renamed to `le`.\nThis template means: Antisymmetry.")


@pytest.fixture(scope="module", autouse=True)
def isolated_db(tmp_path_factory):
    dbdir = tmp_path_factory.mktemp("semdb")
    prior = os.environ.get("SEMANTIC_DB_DIR")
    os.environ["SEMANTIC_DB_DIR"] = str(dbdir)
    import Isabelle_Semantic_Embedding.semantics as S
    S.Semantic_DB._close()
    R = S.SemanticRecord
    S.Semantic_DB[TEMPLATE] = R(EntityKind.THEOREM, "Orderings.ordering.antisym", "x ≤ y", "Antisymmetry.")
    S.Semantic_DB[GLOBAL] = R(EntityKind.THEOREM, "HOL.refl", "t = t", "Reflexivity.")
    S.Semantic_DB[LE] = R(EntityKind.CONSTANT, "Foo.le", "'a ⇒ 'a ⇒ bool", "The order.")
    yield
    S.Semantic_DB._close()
    if prior is None:
        os.environ.pop("SEMANTIC_DB_DIR", None)
    else:
        os.environ["SEMANTIC_DB_DIR"] = prior


class FakeConnection:
    def __init__(self):
        self.request_state = {}
        self.fetches = 0

    async def callback(self, name, arg):
        if name == "Semantic_Store.links":
            self.fetches += 1
            return WIRE
        if name == "IsaMini.contextual_thms":
            return []
        raise AssertionError(f"unexpected callback {name}")

    async def semantic_vector_store(self):
        return SimpleNamespace(emb_provider=SimpleNamespace(default_score=0.1, default_local_score=0.3))


NAMES = {LOCAL: "local.antisym", GLOBAL: "HOL.refl", LE: "Foo.le"}


@pytest.mark.parametrize("uk", [LOCAL, GLOBAL])
def test_query_entity_core_shows_the_owner_functions_record(monkeypatch, uk):
    from IsaMini.AoA import retrieval
    from Isabelle_Semantic_Embedding.semantics import Semantic_DB

    async def key_and_name(connection, tag, name, ctxt=None):
        return uk, NAMES[uk]

    async def no_live_rendering(connection, ctxt, entities):
        return [(None, None, None)]

    monkeypatch.setattr(retrieval, "universal_key_and_name_of", key_and_name)
    monkeypatch.setattr(retrieval, "retrieve_entities_with_diagnostics", no_live_rendering)
    conn = FakeConnection()
    text, is_error, got = asyncio.run(retrieval._query_entity_core(conn, EntityKind.THEOREM, "x"))
    assert not is_error and got == uk
    assert conn.fetches == (1 if uk == LOCAL else 0)       # a stored record needs no links
    if uk == LOCAL:
        assert text == "lemma local.antisym: x ≤ y ⟹ y ≤ x ⟹ x = y\n" + COPY
        assert "The order." not in text      # the entities block is never displayed
    else:
        assert Semantic_DB[uk].interpretation in text and text.startswith("lemma HOL.refl:")


def test_query_entity_core_of_a_constant_never_fetches_the_links(monkeypatch):
    from IsaMini.AoA import retrieval

    async def key_and_name(connection, tag, name, ctxt=None):
        return LE, "Foo.le"

    async def no_live_rendering(connection, ctxt, entities):
        return [(None, None, None)]

    monkeypatch.setattr(retrieval, "universal_key_and_name_of", key_and_name)
    monkeypatch.setattr(retrieval, "retrieve_entities_with_diagnostics", no_live_rendering)
    conn = FakeConnection()
    text, is_error, got = asyncio.run(retrieval._query_entity_core(conn, EntityKind.CONSTANT, "le"))
    assert not is_error and got == LE and "The order." in text and conn.fetches == 0


def _state(monkeypatch):
    from IsaMini.AoA import model
    state = model.Minilang_State(FakeConnection(), "s0")
    model._session_var.set(SimpleNamespace(enable_read_memory=True))

    async def resolved(entities):
        return [((SimpleNamespace(unicode=n), [], [], [], True), None, None) for _, n in entities]

    monkeypatch.setattr(state, "_retrieve_entity_with_diagnostics", resolved)
    monkeypatch.setattr(state, "_make_retrieved_entity",
                        lambda kind, name, info, score, interp, **kw: (name, interp))
    return model, state


def test_semantic_knn_exact_name_uses_the_owner_function(monkeypatch):
    model, state = _state(monkeypatch)

    async def members(connection, name, limit, ctxt, kind):
        return 2, [(LOCAL, "local.antisym"), (GLOBAL, "HOL.refl")]

    monkeypatch.setattr(model, "key_of_theorems", members)
    out, _, _ = asyncio.run(state.semantic_knn_counted(None, 5, [EntityKind.THEOREM], exact_name="antisym"))
    assert out == [("local.antisym", " ".join(COPY.split())), ("HOL.refl", "Reflexivity.")]


def test_semantic_knn_pattern_only_uses_the_owner_function(monkeypatch):
    import Isabelle_RPC_Host.context as C
    model, state = _state(monkeypatch)

    async def entities(connection, kinds, **kw):
        return ([(LOCAL, "local.antisym", True), (TEMPLATE, "Orderings.ordering.antisym", False),
                 (GLOBAL, "HOL.refl", False)], [])

    monkeypatch.setattr(C, "entities_of", entities)
    out, _, total = asyncio.run(state.semantic_knn_counted(None, 5, [EntityKind.THEOREM],
                                                           term_patterns=["_ = _"]))
    # the template of the linked local fact is hidden, as lookup hides it
    assert out == [("local.antisym", " ".join(COPY.split())), ("HOL.refl", "Reflexivity.")]
    assert total == 2

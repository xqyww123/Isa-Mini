"""A rendered entity's definition comes from the position IsaMini.retrieve_entity
reports for it: the Useful-lemmas path (`retrieve_entities_by_name` then
`_render_fetched_entities`) hands that position to `_definition_at`, and
`_format_fetched_entity` never fetches one for a proof method or a theorem
collection, or without a position.  A fake connection; no Isabelle, no LLM.
Run with  python -m pytest contrib/Isa-Mini/IsaMini/AoA/test_definition_position.py
"""
import asyncio
from io import StringIO
from types import SimpleNamespace

import pytest

from Isabelle_RPC_Host.position import IsabellePosition
from Isabelle_RPC_Host.universal_key import EntityKind

POS = ("/a/T.thy", 7, 120)
SOURCE = 'definition foo :: nat where "foo = 0"'


class FakeConnection:
    """Answers IsaMini.retrieve_entity with a display and (uk, POS) per name."""

    async def callback(self, name, arg):
        assert name == "IsaMini.retrieve_entity", name
        _, entities = arg
        return [((n, ["foo = 0"], ["simp"], [], False), (b"\x01" * 32, POS), None)
                for _, n in entities]


@pytest.fixture
def world(monkeypatch):
    from IsaMini.AoA import model, retrieval
    state = model.Minilang_State(FakeConnection(), "s0")
    session = SimpleNamespace(seen_abbreviations=set(), seen_commands={},
                              retrieval_state=lambda: state)
    asked: list[IsabellePosition] = []

    async def definition_at(connection, pos):
        asked.append(pos)
        return (SOURCE, IsabellePosition(0, 100, pos.file))

    monkeypatch.setattr(retrieval, "_definition_at", definition_at)
    return model, retrieval, state, session, asked


def test_useful_lemmas_path_passes_the_retrieved_position(world):
    _, retrieval, state, session, asked = world
    entities = asyncio.run(state.retrieve_entities_by_name(["foo_def"]))
    assert [e.position for e in entities] == [IsabellePosition(7, 120, "/a/T.thy")]
    buf = StringIO()
    asyncio.run(retrieval._render_fetched_entities(session, state, entities, buf))
    assert asked == [IsabellePosition(7, 120, "/a/T.thy")]
    assert SOURCE in buf.getvalue()


@pytest.mark.parametrize("kind, position, fetched", [
    (EntityKind.CONSTANT, IsabellePosition(7, 120, "/a/T.thy"), True),
    (EntityKind.METHOD, IsabellePosition(7, 120, "/a/T.thy"), False),
    (EntityKind.THEOREM_COLLECTION, IsabellePosition(7, 120, "/a/T.thy"), False),
    (EntityKind.CONSTANT, None, False),
])
def test_no_definition_for_methods_collections_or_without_a_position(world, kind, position, fetched):
    model, retrieval, state, session, asked = world
    info = (model.IsaTerm.from_isabelle("foo"), [], [], [], False)
    f = state._make_retrieved_entity(kind, "T.foo", info, 0.5, None, position=position)
    asyncio.run(retrieval._format_fetched_entity(f, StringIO(), session=session,
                                                 ml_state=state, def_info=True))
    assert bool(asked) == fetched

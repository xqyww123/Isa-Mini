"""Unit tests of the Python half of user operations and tasks
(docs/USER_OPERATIONS.md, sections 3, 4.1, 4.2, 5.2, 5.3): what `@proof_operation`
and `@aoa_task` refuse at decoration, the call's operation table and what
`Parse_Nodes` reports on a miss, the tag-21 message, the one-subgoal rule of a
`Leaf`, the gate of a `SubgoalMaker`, and the call's `edit` schema with the
forms each provider derives from it.  No REPL, no RPC.
"""
import asyncio
import os
import sys
import types
from typing import Any, NotRequired, TypedDict, cast

import jsonschema
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from IsaMini.AoA import model                                                # noqa: E402
from IsaMini.AoA.model import (                                              # noqa: E402
    AoA_Error, ArgumentError_UnknownProofOperation, BUILTIN_OPERATIONS, InternalError,
    IsabelleError, Leaf, Message, Minilang_Operation, OPERATION_REGISTRY,
    OPERATION_REGISTRY_BY_CLS, Parse_Op_List, Runtime, Session, SubgoalMaker, StdBlock,
    UserNode, _check_builtins_advertised, proof_operation, unpack_message, _session_var)
from IsaMini.AoA import task as task_module                                  # noqa: E402
from IsaMini.AoA.task import TASK_REGISTRY, Task, aoa_task                   # noqa: E402


class Sample_ToolArg(TypedDict):
    thought: NotRequired[str]
    method: str


def schema_of(name: str, **extra) -> dict:
    """A well-formed construct_schema for `name`, with `extra` merged in."""
    return {
        "type": "object", "additionalProperties": False,
        "description": "apply a method",
        "properties": {
            "operation": {"const": name, "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "method": {"type": "string"}},
        "required": ["operation", "thought", "method"],
        **extra}


class _Hooks:
    """The hooks a block base demands, so that a sample class is not abstract."""
    def quickview_title(self): return "sample"
    def _print_header(self, *a, **k): return 0
    def print(self, *a, **k): return 0
    def _beginning_opr_err_msgs(self, err): return model.FailureReason("")
    def _child_refresh_failure_err_msgs(self, child): return model.FailureReason("")


@pytest.fixture
def registries():
    """Snapshot the process-wide registries; restore them after the test."""
    ops, by_cls, tasks = dict(OPERATION_REGISTRY), dict(OPERATION_REGISTRY_BY_CLS), dict(TASK_REGISTRY)
    yield
    OPERATION_REGISTRY.clear(); OPERATION_REGISTRY.update(ops)
    OPERATION_REGISTRY_BY_CLS.clear(); OPERATION_REGISTRY_BY_CLS.update(by_cls)
    TASK_REGISTRY.clear(); TASK_REGISTRY.update(tasks)


def sample_leaf(name: str = "SampleLeaf", **extra):
    @proof_operation(name, Sample_ToolArg)
    class Sample(UserNode, _Hooks, Leaf):
        construct_schema = schema_of(name, **extra)
        def __init__(self, config, arg):
            super().__init__(config, arg.get("thought", ""))
            self.method = arg["method"]
        def payload(self): return self.method
    return Sample


def bare_session(*names: str, tactics: 'tuple[tuple[str, str, str, bool, bytes], ...]' = ()) -> Session:
    """A Session with only a Runtime over the given user operations and tactic
    whitelist, bound as the current one."""
    s = object.__new__(Session)
    s.runtime = Runtime(names, tactics)
    _session_var.set(s)
    return s


# --- decoration -------------------------------------------------------------------

def test_a_well_formed_class_registers(registries):
    cls = sample_leaf()
    assert OPERATION_REGISTRY["SampleLeaf"].cls is cls
    assert cls.operation_name() == "SampleLeaf"


def test_a_name_held_by_another_class_is_refused(registries):
    with pytest.raises(ValueError, match='Proof operation "Have" is already registered by'):
        sample_leaf("Have")


def test_the_same_class_reimported_registers_again(registries):
    sample_leaf()
    sample_leaf()      # same module and qualified name: a re-import


def test_an_abstract_class_is_refused(registries):
    with pytest.raises(TypeError, match="is abstract; missing: .*payload"):
        @proof_operation("Abstract1", Sample_ToolArg)
        class NoPayload(UserNode, _Hooks, Leaf):
            construct_schema = schema_of("Abstract1")


def test_a_base_listed_before_the_mixin_is_refused(registries):
    with pytest.raises(TypeError, match="is abstract"):
        @proof_operation("Abstract2", Sample_ToolArg)
        class BaseFirst(Leaf, UserNode, _Hooks):   # Leaf's abstract the_operation wins
            construct_schema = schema_of("Abstract2")
            def payload(self): return ""


@pytest.mark.parametrize("extra, reason", [
    ({"additionalProperties": True}, "must set additionalProperties to false"),
    ({"properties": {"operation": {"const": "Other", "type": "string"}, "method": {"type": "string"}}},
     'must declare properties.operation as the const "Bad"'),
    ({"properties": {"operation": {"const": "Bad", "type": "string"},
                     "steps": {"$ref": "#/$defs/Operation"}}},
     "must not refer to #/\\$defs/Operation"),
    ({"properties": {"operation": {"const": "Bad", "type": "string"},
                     "x": {"$ref": "#/$defs/NoSuchDef"}}},
     "refers to #/\\$defs/NoSuchDef, which the base schema does not define"),
    ({"type": 42}, "is not a valid JSON schema"),
])
def test_a_bad_schema_is_refused(registries, extra, reason):
    with pytest.raises(ValueError, match='User operation "Bad": construct_schema ' + reason):
        sample_leaf("Bad", **extra)


def test_a_name_of_the_base_schema_is_refused(registries):
    with pytest.raises(ValueError, match='the name "Proof" is a definition of the base schema'):
        sample_leaf("Proof")


def test_a_class_without_a_schema_is_refused(registries):
    with pytest.raises(ValueError, match="defines no construct_schema dict"):
        @proof_operation("NoSchema", Sample_ToolArg)
        class NoSchema(UserNode, _Hooks, Leaf):
            def payload(self): return ""


def test_tasks_register_and_refuse_duplicates(registries):
    assert TASK_REGISTRY["usual"] is task_module.UsualTask
    assert TASK_REGISTRY["learning"] is task_module.LearningTask
    with pytest.raises(ValueError, match='Task "usual" is already registered by'):
        @aoa_task("usual")
        class Another(Task):
            def system_prompt(self, session): return None
    with pytest.raises(TypeError, match='Task "abstract": .* is abstract'):
        @aoa_task("abstract")
        class Abstract(Task):
            pass
    assert isinstance(TASK_REGISTRY["usual"](""), task_module.UsualTask)


# --- the call's table -------------------------------------------------------------

def test_the_table_starts_with_the_builtins_only(registries):
    sample_leaf()
    rt = Runtime()
    assert "Have" in rt.operations and "SampleLeaf" not in rt.operations
    assert dict(rt.operations) == dict(BUILTIN_OPERATIONS)


def test_a_builtins_subclass_registered_later_is_not_a_builtin(registries):
    # the built-ins are the operations tools/cc_edit.jsonc has an entry for; a
    # class that registers under another name without being a UserNode is
    # neither built-in nor usable (the one exception is Tactic, below)
    Have = OPERATION_REGISTRY["Have"].cls
    @proof_operation("MyHave", Sample_ToolArg)
    class MyHave(Have):
        pass
    assert "MyHave" not in Runtime().operations
    with pytest.raises(AoA_Error, match='User operation "MyHave": its node class .*MyHave is not a UserNode'):
        Runtime(["MyHave"])


def test_the_table_keeps_the_order_given_and_refuses(registries):
    # the order given is neither the order the classes were registered in nor name order
    a = sample_leaf("Alpha"); b = sample_leaf("Beta")
    rt = Runtime(["Beta", "Alpha"])
    assert list(rt.operations)[-2:] == ["Beta", "Alpha"]
    assert rt.operations["Alpha"].cls is a and rt.operations["Beta"].cls is b
    with pytest.raises(AoA_Error, match='User operation "Nope": no imported Python package'):
        Runtime(["Nope"])
    with pytest.raises(AoA_Error, match='User operation "Have": its node class Have is not a UserNode'):
        Runtime(["Have"])


def test_parse_reports_the_tables_names_on_a_miss(registries):
    sample_leaf()
    bare_session()
    with pytest.raises(ArgumentError_UnknownProofOperation) as e:
        Parse_Op_List([{"operation": "SampleLeaf", "method": "simp"}], "test")
    assert "'SampleLeaf'" not in str(e.value) and "'Have'" in str(e.value)
    bare_session("SampleLeaf")
    parsed = Parse_Op_List([{"operation": "SampleLeaf", "method": "simp"}], "test")
    assert parsed[0].cls is OPERATION_REGISTRY["SampleLeaf"].cls
    with pytest.raises(ArgumentError_UnknownProofOperation) as e:
        Parse_Op_List([{"operation": "Nope"}], "test")
    assert "'SampleLeaf'" in str(e.value)


# --- the operation and its messages ---------------------------------------------------

def test_the_operation_is_the_user_command_with_the_payload(registries):
    cls = sample_leaf()
    node = object.__new__(cls); node.method = "(simp)"
    assert node.the_operation() == Minilang_Operation("USER", ("SampleLeaf", "(simp)"))
    assert node.beginning_opr() == Minilang_Operation("USER", ("SampleLeaf", "(simp)"))


class Own_Msg(Message):
    def __init__(self, value): self.value = value


def test_tag_21_goes_to_the_running_operations_class(registries):
    cls = sample_leaf()
    with pytest.raises(InternalError, match="arrived for a built-in step"):
        unpack_message((21, 5), None)
    with pytest.raises(InternalError, match='User operation "SampleLeaf": its pack_message reported a message its node class does not decode.'):
        unpack_message((21, 5), cls)
    class Decoding(cls):
        @classmethod
        def unpack_own_message(cls, value): return Own_Msg(value)
    assert unpack_message((21, 5), Decoding).value == 5
    assert isinstance(unpack_message((1, 2), cls), model.Goals_Msg)


def test_a_leaf_may_leave_at_most_one_subgoal(registries):
    cls = sample_leaf()
    node = object.__new__(cls)
    async def execute(opr, dest): pass
    state = types.SimpleNamespace(execute=execute)
    opr = Minilang_Operation("USER", ("SampleLeaf", "(rule conjI)"))
    asyncio.run(node._execute_opr(state, opr, types.SimpleNamespace(new_subgoals_count=1)))
    asyncio.run(node._execute_opr(state, opr, types.SimpleNamespace(new_subgoals_count=0)))
    with pytest.raises(IsabelleError) as e:
        asyncio.run(node._execute_opr(state, opr, types.SimpleNamespace(new_subgoals_count=2)))
    assert e.value.errors == ['User operation "SampleLeaf" left 2 subgoals, but its node class is a '
                              'Leaf, which may leave at most one; the plugin must make it a SubgoalMaker.']


def test_a_subgoal_maker_is_gated_as_branch_is(registries):
    @proof_operation("SampleMaker", Sample_ToolArg)
    class Maker(UserNode, _Hooks, SubgoalMaker):
        construct_schema = schema_of("SampleMaker")
        def __init__(self, config, arg):
            super().__init__(config, arg.get("thought", ""), [])
        def payload(self): return ""
    node = object.__new__(Maker)
    v = types.SimpleNamespace(unicode="?x")
    # the variable sits in a sibling goal only: seen with whole=True, not otherwise
    async def sibling_only(whole): return ([v], []) if whole else ([], [])
    async def without(whole): return ([], [])
    assert asyncio.run(node.can_operate_on_schematic_goal(
        types.SimpleNamespace(schematic_variables_of=without), None)) is None
    msg = asyncio.run(node.can_operate_on_schematic_goal(
        types.SimpleNamespace(schematic_variables_of=sibling_only), None))
    assert msg == model._gate_rejection("SampleMaker", ["?x"])
    # a Leaf keeps Node's default: allowed
    leaf = object.__new__(sample_leaf())
    assert asyncio.run(leaf.can_operate_on_schematic_goal(
        types.SimpleNamespace(schematic_variables_of=sibling_only), None)) is None


def test_a_subgoal_maker_supplies_the_ending_hook_default(registries):
    @proof_operation("SampleMaker2", Sample_ToolArg)
    class Maker(UserNode, _Hooks, SubgoalMaker):
        construct_schema = schema_of("SampleMaker2")
        def __init__(self, config, arg):
            super().__init__(config, arg.get("thought", ""), [])
        def payload(self): return ""
    with pytest.raises(InternalError, match="A Maker doesn't have an ending operation"):
        object.__new__(Maker)._ending_opr_err_msgs(IsabelleError([""], None))
    for name in ("SplitConjs", "InferenceRule", "Branch", "CaseSplit", "Induction"):
        with pytest.raises(InternalError, match=f"A {name} doesn't have an ending operation"):
            object.__new__(OPERATION_REGISTRY[name].cls)._ending_opr_err_msgs(IsabelleError([""], None))


# --- the edit schema of the call (section 5.3) --------------------------------------

from IsaMini.AoA import mcp_http_server as mcp                                   # noqa: E402
from IsaMini.AoA.driver_openai_api import _flatten_edit_schema_deepseek, _strictify_schema  # noqa: E402
from IsaMini.AoA.edit_schema import BASE_EDIT_SCHEMA                             # noqa: E402


def sample_block(name: str = "SampleBlock"):
    """A StdBlock plugin class with a sub-proof field, named `proof` by convention."""
    @proof_operation(name, Sample_ToolArg)
    class Block(UserNode, _Hooks, StdBlock):
        construct_schema = schema_of(name, properties={
            "operation": {"const": name, "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "method": {"type": "string"},
            "proof": {"$ref": "#/$defs/Proof"}})
        def __init__(self, config, arg, parsed_proof):
            super().__init__(config, arg.get("thought", ""), [])
        def payload(self): return ""
        def _ending_opr_err_msgs(self, err): return model.FailureReason("")
    return Block


def session_with(*names: str, tactics: 'tuple[tuple[str, str, str, bool, bytes], ...]' = ()) -> Session:
    s = bare_session(*names, tactics=tactics)
    s._can_offer_dispatch_tools = lambda: True
    return s


def test_the_calls_edit_schema_carries_its_user_operations(registries):
    sample_block(); sample_leaf()          # registered in the other order
    s = session_with("SampleLeaf", "SampleBlock")
    assert "schema" not in mcp._TOOL_SCHEMAS["edit"]
    schema = mcp._tool_schemas_for(s)["edit"]["schema"]
    assert schema["$defs"]["SampleLeaf"] == OPERATION_REGISTRY["SampleLeaf"].cls.construct_schema
    assert schema["$defs"]["Operation"]["anyOf"][-2:] == [      # the order given
        {"$ref": "#/$defs/SampleLeaf"}, {"$ref": "#/$defs/SampleBlock"}]
    assert "SampleLeaf" not in BASE_EDIT_SCHEMA["$defs"]              # the base is untouched
    plain = mcp._tool_schemas_for(session_with())["edit"]["schema"]
    assert "SampleLeaf" not in plain["$defs"]                          # another call sees nothing


def test_every_derived_form_carries_the_user_operation_and_no_ref(registries):
    sample_leaf(); sample_block()
    schema = mcp._tool_schemas_for(session_with("SampleLeaf", "SampleBlock"))["edit"]["schema"]
    flat = mcp._flatten_edit_schema(schema)
    forms = {
        "gemini": flat,
        "openai": _strictify_schema(flat),
        "codex": mcp._merge_edit_operations_schema(flat),
        "deepseek": _flatten_edit_schema_deepseek(schema)}
    for name, form in forms.items():
        mcp._assert_no_refs(form)
        text = json.dumps(form)
        assert '"SampleLeaf"' in text and '"SampleBlock"' in text, name
    assert "SampleLeaf" in forms["codex"]["properties"]["proof_operations"]["items"]["properties"]["operation"]["enum"]
    # DeepSeek drops a plugin's sub-proof field as it drops Have's: by its name, `proof`
    ops = {m["properties"]["operation"]["enum"][0]: m
           for m in forms["deepseek"]["properties"]["proof_operations"]["items"]["anyOf"]}
    assert "proof" not in ops["SampleBlock"]["properties"] and "method" in ops["SampleBlock"]["properties"]
    assert "proof" not in ops["Have"]["properties"]


def test_the_deepseek_form_of_the_base_drops_exactly_the_sub_proof_fields():
    """Pins the rule on the base schema: every operation keeps its properties minus
    `proof`/`proofs`, and Branch's case objects lose exactly `proof`."""
    form = _flatten_edit_schema_deepseek(BASE_EDIT_SCHEMA)
    mcp._assert_no_refs(form)
    members = {m["properties"]["operation"]["enum"][0]: m
               for m in form["properties"]["proof_operations"]["items"]["anyOf"]}
    for ref in BASE_EDIT_SCHEMA["$defs"]["Operation"]["anyOf"]:
        name = ref["$ref"].split("/")[-1]
        base_props = set(BASE_EDIT_SCHEMA["$defs"][name]["properties"])
        assert set(members[name]["properties"]) == base_props - {"proof", "proofs"}, name
    case = members["Branch"]["properties"]["cases"]["items"]["properties"]
    base_case = BASE_EDIT_SCHEMA["$defs"]["Branch"]["properties"]["cases"]["items"]["properties"]
    assert set(case) == set(base_case) - {"proof"}


def member_of(form: dict, name: str) -> dict:
    """The operation `name`'s member of a flattened form's proof_operations
    (DeepSeek's form spells the name as a one-value enum, the others as a const)."""
    for m in form["properties"]["proof_operations"]["items"]["anyOf"]:
        operation = m["properties"]["operation"]
        if operation.get("enum") == [name] or operation.get("const") == name:
            return m
    raise KeyError(name)


def test_the_deepseek_form_keeps_a_plugin_field_named_like_a_schema_keyword(registries):
    """`default`, `minItems`, `maxItems`, `properties` are read as schema keywords
    only where a schema keyword can stand; a plugin's field under such a name
    stays, untouched, in DeepSeek's and OpenAI's forms, which stay valid schemas."""
    name = "WithDefault"
    @proof_operation(name, Sample_ToolArg)
    class WithDefault(UserNode, Leaf):
        construct_schema = schema_of(name, properties={
            "operation": {"const": name, "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "method": {"type": "string"},
            "default": {"type": "string", "default": "x"},
            "properties": {"type": "string"}})
        def payload(self): return ""
    schema = mcp._tool_schemas_for(session_with(name))["edit"]["schema"]
    deepseek = _flatten_edit_schema_deepseek(schema)
    member = member_of(deepseek, name)
    assert set(member["properties"]) == {"operation", "thought", "method", "default", "properties"}
    assert "default" not in member["properties"]["default"]        # the keyword
    assert member["properties"]["properties"] == {"type": "string"}  # no fake fields
    jsonschema.Draft202012Validator.check_schema(deepseek)
    openai = _strictify_schema(mcp._flatten_edit_schema(schema))
    field = member_of(openai, name)["properties"]["properties"]   # nullable there: optional
    assert field["type"] == ["string", "null"] and not {"required", "additionalProperties"} & set(field)
    jsonschema.Draft202012Validator.check_schema(openai)


def test_the_deepseek_form_appends_the_simplify_hint(registries):
    """A field named `simplify` gets " Most cases: true." appended to its description."""
    name = "WithSimplify"
    @proof_operation(name, Sample_ToolArg)
    class WithSimplify(UserNode, Leaf):
        construct_schema = schema_of(name, properties={
            "operation": {"const": name, "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "method": {"type": "string"},
            "simplify": {"type": "boolean", "description": "d"}})
        def payload(self): return ""
    form = _flatten_edit_schema_deepseek(mcp._tool_schemas_for(session_with(name))["edit"]["schema"])
    assert member_of(form, name)["properties"]["simplify"]["description"] == "d Most cases: true."


def test_the_builtins_must_match_the_advertised_operations():
    """The import-time check names what is decorated but not advertised, and the reverse."""
    import copy
    base = copy.deepcopy(BASE_EDIT_SCHEMA)
    alternatives = base["$defs"]["Operation"]["anyOf"]
    dropped = alternatives.pop()["$ref"].removeprefix("#/$defs/")
    alternatives.append({"$ref": "#/$defs/Phantom"})
    with pytest.raises(ImportError) as e:
        _check_builtins_advertised(BUILTIN_OPERATIONS, base)
    assert f"decorated only: ['{dropped}']" in str(e.value)
    assert "advertised only: ['Phantom']" in str(e.value)
    _check_builtins_advertised(BUILTIN_OPERATIONS, BASE_EDIT_SCHEMA)   # the real pair agrees


@pytest.mark.parametrize("flatten", [mcp._flatten_edit_schema, _flatten_edit_schema_deepseek],
                         ids=["gemini", "deepseek"])
def test_each_flattening_checks_its_own_output(registries, flatten):
    """The decorator admits a construct_schema carrying its own `$defs`; only
    the flattening's own `_assert_no_refs`, at its end, catches what is left."""
    name = "WithDefs"
    @proof_operation(name, Sample_ToolArg)
    class WithDefs(UserNode, Leaf):
        construct_schema = schema_of(name, **{"$defs": {"Unused": {"type": "string"}}})
        def payload(self): return ""
    schema = mcp._tool_schemas_for(session_with(name))["edit"]["schema"]
    with pytest.raises(AssertionError, match=r"\$defs"):
        flatten(schema)


import json  # noqa: E402


# --- the providers' seams: each a pure function of the schema it is handed ---------

def calls_schema():
    sample_leaf()
    return mcp._tool_schemas_for(session_with("SampleLeaf"))["edit"]["schema"]


def test_openai_derives_its_form_from_the_calls_schema(registries):
    from IsaMini.AoA import driver_openai_api as oa
    form = oa.OpenAIBase._strict_schema(None, "edit", calls_schema())   # self unused for edit
    mcp._assert_no_refs(form)
    assert '"SampleLeaf"' in json.dumps(form)


def test_deepseek_derives_its_form_from_the_calls_schema(registries):
    from IsaMini.AoA import driver_openai_api as oa
    form = oa.DeepSeekProvider._strict_schema(None, "edit", calls_schema())
    mcp._assert_no_refs(form)
    assert '"SampleLeaf"' in json.dumps(form)


def test_codex_derives_its_form_from_the_calls_schema(registries):
    from IsaMini.AoA import driver_codex as cx
    form = cx.Codex_Driver.transform_tool_schema(None, "edit", calls_schema())
    mcp._assert_no_refs(form)
    assert "SampleLeaf" in form["properties"]["proof_operations"]["items"]["properties"]["operation"]["enum"]


def test_gemini_derives_its_form_from_the_calls_schema(registries):
    pytest.importorskip("google.genai")
    from IsaMini.AoA import driver_gemini as gm
    tools = gm.GeminiProvider.format_tools(None, {"edit": {"description": "", "schema": calls_schema()}})
    decl = tools[0].function_declarations[0]
    mcp._assert_no_refs(decl.parameters_json_schema)
    assert '"SampleLeaf"' in json.dumps(decl.parameters_json_schema)


# --- the Tactic operation and its whitelist (docs/TACTIC_DESIGN.md) ------------------

import logging  # noqa: E402
from IsaMini.AoA.model import ArgumentError, TOOL_SEARCH                     # noqa: E402
from Isabelle_RPC_Host.universal_key import EntityKind                       # noqa: E402


def method_key(full: str) -> bytes:
    """A METHOD universal key as ML builds one -- 16 bytes of theory hash, the
    kind's tag, the full name in UTF-8; the hash is immaterial here."""
    return b"\x00" * 16 + bytes([int(EntityKind.METHOD)]) + full.encode()


SIMP = ("simp", "HOL.simp", "rewrite the goal with the simplifier", False, method_key("HOL.simp"))
INDUCTION = ("induction", "HOL.induction", "prove by induction on a variable", True, method_key("HOL.induction"))


def test_tactic_is_never_a_user_operation(registries):
    with pytest.raises(AoA_Error, match='User operation "Tactic": its node class .*Tactic is not a UserNode'):
        Runtime(["Tactic"])


@pytest.mark.parametrize("name", ["tactic", "aoa", "auto"])
def test_a_tactic_outside_the_whitelist_is_refused_at_parse_time(registries, name):
    """On every driver, before any Isabelle call: the bare session has no connection."""
    bare_session(tactics=(SIMP,))
    op = {"operation": "Tactic", "thought": "t", "tactic": name}
    with pytest.raises(ArgumentError, match=r"`proof_operations\[0\] \(Tactic\)\.tactic` must be one of `simp`"):
        Parse_Op_List([op], "proof_operations")
    have = {"operation": "Have", "thought": "t", "name": "h",
            "statement": {"english": "trivial", "conclusion": "True"}, "proof": [dict(op)]}
    with pytest.raises(ArgumentError, match=r"\(Have\)\.proof\[0\] \(Tactic\)\.tactic` must be one of `simp`"):
        Parse_Op_List([have], "proof_operations")


def test_an_empty_whitelist_has_no_tactic_operation(registries):
    rt = Runtime([], [])
    assert "Tactic" not in rt.operations and rt.tactics == {} and rt.tactics_by_full == {}
    schema = mcp._edit_schema_for(rt)
    assert "Tactic" not in schema["$defs"]
    assert {"$ref": "#/$defs/Tactic"} not in schema["$defs"]["Operation"]["anyOf"]


def test_the_whitelist_places_tactic_with_its_enum(registries):
    sample_leaf()
    rt = Runtime(["SampleLeaf"], [INDUCTION, SIMP])
    assert list(rt.operations) == [*BUILTIN_OPERATIONS, "Tactic", "SampleLeaf"]
    assert list(rt.tactics) == ["induction", "simp"]                 # whitelist order, agent-visible names
    assert rt.tactics["simp"].full == "HOL.simp"
    assert rt.tactics_by_full["HOL.simp"] is rt.tactics["simp"]
    schema = mcp._edit_schema_for(rt)
    assert schema["$defs"]["Tactic"]["properties"]["tactic"]["enum"] == ["induction", "simp"]
    assert schema["$defs"]["Operation"]["anyOf"][-2:] == [{"$ref": "#/$defs/Tactic"}, {"$ref": "#/$defs/SampleLeaf"}]
    assert model.Tactic.construct_schema["properties"]["tactic"]["enum"] == []   # the template is untouched
    rt.activate_tactics([])                                           # a re-activation keeps the order
    assert list(rt.operations) == [*BUILTIN_OPERATIONS, "SampleLeaf"]
    assert "Tactic" not in mcp._edit_schema_for(rt)["$defs"]
    rt.activate_tactics([SIMP])
    assert list(rt.operations) == [*BUILTIN_OPERATIONS, "Tactic", "SampleLeaf"]


PHI_REASON = ("\\<phi>reason", "PLPR.\\<phi>reason", "run the phi reasoner", True, method_key("PLPR.\\<phi>reason"))


def test_a_symbol_name_is_shown_in_unicode_and_read_in_either_notation(registries):
    """The agent-visible name is an IsaTerm: the agent sees `.unicode` (the
    enum, the prompt block, the node, a rejection), the whitelist is keyed by
    `.ascii`, and a spelling the agent supplies is read by ascii_of_unicode as
    every name is -- in either notation."""
    s = session_with(tactics=(PHI_REASON,))
    s.role = model.Role_Major()
    rt = s.runtime
    assert list(rt.tactics) == ["\\<phi>reason"]
    entry = rt.tactics["\\<phi>reason"]
    assert (entry.name.unicode, entry.name.ascii) == ("φreason", "\\<phi>reason")
    assert rt.tactics_by_full["PLPR.\\<phi>reason"] is entry
    assert mcp._edit_schema_for(rt)["$defs"]["Tactic"]["properties"]["tactic"]["enum"] == ["φreason"]
    assert "- φreason: run the phi reasoner" in s._tactic_prompt_block()
    cfg = model.NodeConfig(local_step="1", ml_state=cast(Any, None), parent=None)
    for spelling in ("φreason", "\\<phi>reason"):
        [parsed] = Parse_Op_List([{"operation": "Tactic", "thought": "t", "tactic": spelling}], "proof_operations")
        node = cast(model.Tactic, parsed.factory(cfg))
        assert node.tactic is entry.name and node.tactic_full == "PLPR.\\<phi>reason"
        assert node.quickview_title() == "Tactic (φreason)"
    with pytest.raises(ArgumentError, match=r"`proof_operations\[0\] \(Tactic\)\.tactic` must be one of `φreason`"):
        Parse_Op_List([{"operation": "Tactic", "thought": "t", "tactic": "\\<phi>reasoner"}], "proof_operations")
    with pytest.raises(ArgumentError, match=r"`proof_operations\[0\] \(Tactic\)\.tactic` must be one of `φreason`"):
        Parse_Op_List([{"operation": "Tactic", "thought": "t", "tactic": "PLPR.\\<phi>reason"}], "proof_operations")


def test_the_builtins_are_the_operations_of_the_base_schema(registries):
    assert "Tactic" in OPERATION_REGISTRY and "Tactic" not in BUILTIN_OPERATIONS
    assert set(BUILTIN_OPERATIONS) == {n for n in OPERATION_REGISTRY if n in BASE_EDIT_SCHEMA["$defs"]}
    model._check_construct_schema('Built-in operation "Tactic"', "Tactic", model.Tactic.construct_schema)


def test_each_provider_form_carries_the_tactic_enum(registries):
    from IsaMini.AoA import driver_openai_api as oa
    schema = mcp._tool_schemas_for(session_with(tactics=(SIMP,)))["edit"]["schema"]
    forms = {
        "claude code": schema,
        "gemini": mcp._flatten_edit_schema(schema),
        "openai": oa.OpenAIBase._strict_schema(None, "edit", schema),
        "deepseek": oa.DeepSeekProvider._strict_schema(None, "edit", schema),
    }
    for name, form in forms.items():
        text = json.dumps(form)
        assert '"Tactic"' in text and '"simp"' in text and "HOL.simp" not in text, name


@pytest.mark.parametrize("read_memory", [True, False])
def test_the_proof_tactic_kind_follows_the_query_entries(registries, read_memory):
    def kinds_of(session):
        return (mcp._tool_schemas_for(session)[TOOL_SEARCH]["schema"]
                ["properties"]["queries"]["items"]["properties"]["kinds"]["items"]["enum"])
    for tactics, offered in [((), False), ((INDUCTION,), False), ((SIMP,), True), ((INDUCTION, SIMP), True)]:
        s = session_with(tactics=tactics)
        s.enable_read_memory = read_memory
        s.enable_write_memory = read_memory
        kinds = kinds_of(s)
        assert ("proof tactic" in kinds) is offered, tactics
        assert ("experience" in kinds) is read_memory
        assert "proof method" not in kinds


def test_a_plugin_class_never_probes_post_instantiation(registries):
    class PluginCases(UserNode, _Hooks, model.CaseSplit_Like):
        construct_schema = schema_of("PluginCases")
        def payload(self): return ""
    assert PluginCases._probes_post_insts is False
    assert model.Tactic_Like._probes_post_insts and model.CaseSplit_Like._probes_post_insts
    assert model.SubgoalMaker._probes_post_insts is False


@pytest.fixture
def throwaway_db():
    from IsaMini.AoA.test import _isolated_semantic_db_process
    with _isolated_semantic_db_process() as path:
        yield path


def test_declare_interpretation(throwaway_db, monkeypatch):
    from Isabelle_Semantic_Embedding import semantics
    from Isabelle_Semantic_Embedding.semantics import Semantic_DB, SemanticRecord
    invalidated: list[list[bytes]] = []
    monkeypatch.setattr(semantics, "invalidate_vectors", lambda keys: invalidated.append(list(keys)))
    key = method_key("HOL.simp")
    # a fresh record, the text normalized
    assert Semantic_DB.declare_interpretation(key, "rewrite the goal\n   with the\tsimplifier") is True
    rec = Semantic_DB[key]
    assert rec is not None and rec.kind == EntityKind.METHOD and rec.name == "HOL.simp" and rec.expr is None
    assert rec.interpretation == "rewrite the goal with the simplifier"
    assert invalidated == [[key]]
    # the same text again: neither written nor invalidated
    assert Semantic_DB.declare_interpretation(key, "rewrite the goal  with the simplifier") is False
    assert invalidated == [[key]]
    # a record as the pipeline writes one for a method (it carries `position`):
    # expr cleared, every other field kept, invalidated once
    seeded = SemanticRecord(EntityKind.METHOD, "HOL.simp", "simp", "the pipeline's text",
                            position=("~~/src/HOL/HOL.thy", 10, 1))
    Semantic_DB[key] = seeded
    del invalidated[:]
    assert Semantic_DB.declare_interpretation(key, "the declaration's text") is True
    assert Semantic_DB[key] == seeded._replace(expr=None, interpretation="the declaration's text")
    assert invalidated == [[key]]
    # not a METHOD key
    with pytest.raises(ValueError, match="not a proof-method key"):
        Semantic_DB.declare_interpretation(b"\x00" * 16 + bytes([int(EntityKind.CONSTANT)]) + b"HOL.simp", "x")
    # a deleted record reappears
    Semantic_DB.delete(key)
    assert Semantic_DB[key] is None
    assert Semantic_DB.declare_interpretation(key, "the declaration's text") is True
    rec = Semantic_DB[key]
    assert rec is not None and rec.interpretation == "the declaration's text"


@pytest.mark.parametrize("driver, expected", [
    ("test.no_such_case", ["sync"]),           # the test driver skips the empty-DB hint
    ("no_such_driver", ["hint", "sync"]),      # any other driver: the hint reads the DB first
])
def test_a_failing_sync_fails_the_call(monkeypatch, driver, expected):
    """The sync is its own step, after the empty-DB hint and before the split
    by driver: a failure is the call's failure, seen as the failure itself --
    after the driver lookup, "Test Not Found" or an unknown driver would be
    seen instead; before the hint, the hint would never see an empty DB."""
    from IsaMini.AoA import toplevel
    from Isabelle_Semantic_Embedding import semantics
    seen: list[str] = []

    class Boom(Exception):
        pass

    async def hint(connection):
        seen.append("hint")

    def boom(key, text):
        seen.append("sync")
        raise Boom("the DB is broken")
    monkeypatch.setattr(toplevel, "_ensure_semantic_db", hint)
    monkeypatch.setattr(semantics.Semantic_DB, "declare_interpretation", boom)
    connection = types.SimpleNamespace(server=types.SimpleNamespace(logger=logging.getLogger("test")),
                                       callback=None)
    data = (({}, {}, {}), 0, driver, "", "invocation", "", "",
            (1, 1, 1), ("usual", ""), (True, True), [], [SIMP])
    with pytest.raises(Boom):
        asyncio.run(toplevel.IsaMini_AoA(data, connection))
    assert seen == expected

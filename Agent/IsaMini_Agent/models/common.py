from pydantic import BaseModel, ConfigDict, Field, field_validator, TypeAdapter
from typing import List, Optional, Literal, Union, Annotated

class Variable(BaseModel):
    name: str = Field()
    type: str = Field(default="")

class Statement(BaseModel):
    english: str = Field(
        description="the natural language statement in English"
    )
    isabelle: str = Field(
        description="the formal statement in Isabelle/HOL"
    )
    for_any: List[Variable | str] = Field(
        default=[],
        description="variables that the statement is universally quantified over"
    )

class Fact(BaseModel):
    english: str = Field(
        description="the natural language description of the fact"
    )
    isabelle_expression: str = Field(
        description="the Isabelle/HOL expression of the fact"
    )
    for_any: List[Variable | str] = Field(
        default=[],
        description="variables that the fact is universally quantified over"
    )
    # refer_by: Literal["name", "expression"] = Field(
    #     description="whether the fact is referred to by its name or its expression"
    # )
    # value: str = Field(
    #     description="The name or the expression. For expression, wildcard '_' may be used and any fact matching the pattern will be used."
    # )

# import json
# print(json.dumps(TypeAdapter(Fact).json_schema(), indent=2))
# exit(0)


class ATP(BaseModel):
    lemmas: List[Fact] = Field(default=[])
    model_config = ConfigDict(
        extra="forbid",
        title="Obvious",
        json_schema_extra={
            "description": "The proof is straightforward and follows readily from the supporting lemmas"
        },
    )

class Retrive(BaseModel):
    patterns: List[str] = Field(
        default=[],
        description="patterns that the target facts should match. Use wildcard '_' to match any subterm"
    )
    negative_patterns: List[str] = Field(
        default=[],
        alias="negative patterns",
        description="patterns that the target facts should NOT match",
    )
    names: List[str] = Field(
        default=[],
        description="substrings that the names of the target facts should contain"
    )
    model_config = ConfigDict(
        extra="forbid",
        title="Retrieve",
        json_schema_extra={
            "description": "retrieve facts from the system knowledge-base"
        },
    )

class Simplify(BaseModel):
    operation: Literal["simplify"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    lemmas: List[Fact] = Field(
        default=[],
        description="additional equations and lemmas helpful for the simplification"
    )
    model_config = ConfigDict(
        extra="forbid",
        title="Simplify",
        json_schema_extra={
            "description": "call the system simplifier to rewrite proof goals"
        },
    )

class Rewrite(BaseModel):
    operation: Literal["rewrite"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    equations: List[Fact] = Field(
        default=[],
        description="equations to use, which can be conditioned"
    )
    lemmas: List[Fact] = Field(
        default=[],
        description="lemmas to solve the conditions of the equations"
    )
    model_config = ConfigDict(
        extra="forbid",
        title="Rewrite",
        json_schema_extra={
            "description": "rewrite proof goals by calculation and equations"
        },
    )

class Unfold(BaseModel):
    operation: Literal["unfold"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    targets: List[str] = Field(
        default=[],
        description="the target Isabelle/HOL terms to unfold"
    )
    model_config = ConfigDict(
        extra="forbid",
        title="Unfold",
        json_schema_extra={
            "description": "unfold definitions"
        },
    )

class Witness(BaseModel):
    operation: Literal["witness"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    witnesses: List[str] = Field(
        description="Isabelle/HOL expressions of the witness terms"
    )
    model_config = ConfigDict(
        extra="forbid",
        title="Witness",
        json_schema_extra={
            "description": "provide witnesses to reduce existential proof goals. You still need to prove the goal instantiated with the witnesses later."
        },
    )
    next_step: "Declarative_Operations" | Literal["yield and await proof state", "finished"]  = Field(
        description="the next proof operation to perform. You may yield the generation and await proof state update from user"
    )

class Inference_Rule(BaseModel):
    operation: Literal["inference_rule"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    rule: Fact = Field()
    model_config = ConfigDict(
        extra="forbid",
        title="Inference Rule",
        json_schema_extra={
            "description": "prove using a specific inference rule, e.g., contradiction, or proving equality by antisymmetry."
        },
    )
    next_step: Literal["yield and await proof state", "finished"]  = Field(
        description="You must yield the generation and await proof state update from user"
    )

class Branch(BaseModel):
    operation: Literal["branch"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    cases: List[Statement] = Field()
    model_config = ConfigDict(
        extra="forbid",
        json_schema_extra={
            "description": "split the proof goal into cases"
        },
    )
    next_step: Literal["yield and await proof state", "finished"]  = Field(
        description="You must yield the generation and await proof state update from user"
    )


class Have(BaseModel):
    operation: Literal["have"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    statement: Statement = Field()
    model_config = ConfigDict(
        extra="forbid",
        json_schema_extra={
            "description": "introduce a subgoal"
        },
    )
    next_step: "Declarative_Operations" | Literal["yield and await proof state", "finished"]  = Field(
        description="the next proof operation to perform. You may yield the generation and await proof state update from user"
    )

class Obtain(BaseModel):
    operation: Literal["obtain"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    variables: List[Variable] = Field()
    constraints: List[Statement] = Field()
    model_config = ConfigDict(
        extra="forbid",
        json_schema_extra={
            "description": "introduce variables satisfying the given constraints"
        },
    )
    next_step: "Declarative_Operations" | Literal["yield and await proof state", "finished"]  = Field(
        description="the next proof operation to perform. You may yield the generation and await proof state update from user"
    )


class Case_Analysis(BaseModel):
    operation: Literal["case_analysis"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    target_isabelle_term: str = Field()
    # rule: List[Fact] = Field(
    #     default=[],
    #     description="case-split rules indicating non-standard case-split behavior"
    # )
    model_config = ConfigDict(
        extra="forbid",
        title="Case_Analysis",
        json_schema_extra={
            "description": "case analysis on the value or the structure of a target term"
        },
    )

class Induction(BaseModel):
    operation: Literal["induction"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    target_isabelle_term: str = Field(description="target term of the induction")
    arbitrary: list[str] | None = Field(
        None,
        description="variables to be re-quantified universally in each induction "
        "subgoal, allowing them to take different values in different inductive "
        "cases, rather than being fixed to a single value throughout the entire "
        "induction",
    )
    rule: str | None = Field(
        None,
        description="optional induction rule indicating how the induction should work",
    )
    model_config = ConfigDict(
        extra="forbid",
        title="Induction",
        json_schema_extra={
            "description": "apply induction over the target Isabelle/HOL term"
        },
    )

class Suffices_to_Show(BaseModel):
    operation: Literal["suffices_to_show"] = Field()
    thought: str = Field(
        description="a brief thought that justifies the chosen operation"
    )
    statement: Statement = Field()
    model_config = ConfigDict(
        extra="forbid",
        title="Suffices to Show",
        json_schema_extra={
            "description": "to establish the current goal, it suffices to show a stronger or equivalent statement"
        },
    )

Declarative_Operations = Annotated[
      Have
    | Obtain
    | Branch
    | Case_Analysis
    | Induction
    | Rewrite
    | Simplify
    | Unfold
    | Witness
    | Inference_Rule
    | Suffices_to_Show,
    Field(discriminator="operation"),
]


import json
print(json.dumps(TypeAdapter(Declarative_Operations).json_schema(), indent=2))
exit(0)


class Ingredient(BaseModel):
    name: str = Field(description="Name of the ingredient.")
    quantity: str = Field(description="Quantity of the ingredient, including units.")

    model_config = ConfigDict(
        title="Ingredient",
        json_schema_extra={
            "description": "A single ingredient entry used in a recipe."
        },
    )

class Recipe(BaseModel):
    recipe_name: str = Field(description="The name of the recipe.")
    prep_time_minutes: Optional[int] = Field(description="Optional time in minutes to prepare the recipe.")
    ingredients: List[Ingredient]
    instructions: List[str]


import json
print(json.dumps(Ingredient.model_json_schema(), indent=2))
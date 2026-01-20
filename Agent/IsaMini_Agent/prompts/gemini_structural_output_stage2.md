## Task

Based on your proof sketch above, formalize it into the JSON format specified in the output schema.

### Example
#### ENGLISH
To prove P ⟷ Q, we show both directions: first P → Q, then Q → P.
#### FORMALIZATION
{"operation": "inference_rule", thought: "To show P ⟷ Q, we first apply the rule of biconditional introduction to reduce the proof goal into P → Q and Q → P", rule: {english: "if P → Q and Q → P, then P ⟷ Q", refer_by: "expression", value: "(P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟷ Q"}}

### Example
#### ENGLISH
To prove P ⟷ Q, we show both directions: first P → Q, then Q → P.
#### FORMALIZATION
{"operation": "inference_rule", thought: "To show P ⟷ Q, we first apply the rule of biconditional introduction to reduce the proof goal into P → Q and Q → P", rule: {english: "if P → Q and Q → P, then P ⟷ Q", refer_by: "expression", value: "(P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟷ Q"}}



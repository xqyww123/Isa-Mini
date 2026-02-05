## Task

Based on your proof sketch above, formalize it into the JSON format specified in the output schema.

### Hints
- Formalize "Inference Rule Application" into operation `InferenceRule`
- Formalize "Intermediate Statements" into operation `Have`
- Formalize "Case Analysis" into operation `CaseAnalysis` for structural analysis of terms (like lists, trees) or operation `Branch` for case split of propositions (like $x < 0, x = 0, x > 0$).
- Formalize "Induction" into operation `Induction`
- Formalize "Rewriting" into operation `Rewrite` if provided with specific equations or operation `Unfold` for unfolding specific constants.
- Formalize "Suffices to Show" into operation 
- Formalize "Witness Construction" into operation `Witness`
- Whenever you need to check the proof state after an operation, output `"next_step": "yield and await proof state"` to pause formalization of the next step and request the proof state from the user.


### Example
#### English
To prove P ⟷ Q, we show both directions: first P → Q, then Q → P.
#### Formalization
{"operation": "inference_rule", thought: "To show P ⟷ Q, we first apply the rule of biconditional introduction to reduce the proof goal into P → Q and Q → P.", rule: {english: "if P → Q and Q → P, then P ⟷ Q", "isabelle_expression": "(P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P ⟷ Q", "for_any": ["P","Q"]}, "next_step": "yield and await proof state"}

### Example
#### English
We prove `sqrt 2 ∉ ℚ` by contradiction. Suppose `sqrt 2 ∈ ℚ`. We derive a contradiction.
#### Formalization
{"operation": "inference_rule", thought: "To show `sqrt 2 ∉ ℚ`, we prove it by contradiction.", rule: {english: "To show the negation of a proposition, we first assume it holds and then show contradiction exists.", "isabelle_expression": "(P ⟹ False) ⟹ ¬ P", "for_any": ["P"]}, "next_step": "yield and await proof state"}

### Example
#### English
Write $m = in + k$ where $i,k \in mathbb{N}$ and $0 \leq k < n$.
#### Alternative English
Let i and k be the quotient and remainder when m is divided by n.
#### Alternative English
Let $i,k$ be natural numbers such that `m = i*n + k` and `k < n`.
#### Formalization
{"operation": "obtain", "thought": "Let $i,k\in\mathbb{N}$ satisfy $m=in+k$ with $k<n$.", "variables": [{"name": "i", "type": "nat"}, {"name": "k", "type": "nat"}], "next_step": ...}

### Example
#### English
We prove this by considering three cases: x<0, x=0, x>0.
#### Alternative English
We now consider three cases, depending on whether x is negative, zero, or positive.
#### Formalization
{"operation": "branch", "thought": "We consider three cases: $x<0, x=0, x>0$.", "cases": [{"english": "when x < 0", isabelle: "x < 0"}, {"english": "when x = 0", "isabelle": "x = 0"}, {"english": "when x > 0", isabelle "x > 0"}], "next_step": "yield and await proof state"}

### Example
To prove that 6 divides n³ - n for all positive integers n, we begin by factoring the expression. Notice that n³ - n can be rewritten as n(n² - 1), which further factors into (n - 1) · n · (n + 1). This is simply the product of three consecutive integers.
Now, among any three consecutive integers, at least one must be even, so the product is divisible by 2. Similarly, among any three consecutive integers, exactly one must be divisible by 3, since the three integers cover all residue classes modulo 3. Therefore, the product is divisible by both 2 and 3.
Since 2 and 3 are coprime, their product 6 must also divide the expression. This completes the proof.
### Formalization
{"operation": "have", "thought": "To prove that 6 divides n³ - n for all positive integers n, we begin by factoring the expression. The first step is to rewrite n³ - n as n(n² - 1).", "statement": {"english": "n³ - n equals n(n² - 1)", "isabelle": "n^3 - n = n * (n^2 - 1)"}, "next_step": {"operation": "have", "thought": "We further factor it into (n - 1) · n · (n + 1).", "statement": {"english": "n(n² - 1) equals (n - 1) · n · (n + 1)", "isabelle": "n * (n^2 - 1) = (n - 1) * n * (n + 1)"}, "next_step": {"operation": "have", "thought": "Notice that this is the product of three consecutive integers. We now examine the divisibility of this product by 2 and 3. We start from the following fact.", "statement": {"english": "Among any three consecutive integers, at least one must be even.", "isabelle": "∀m. even m ∨ even (Suc m) ∨ even (Suc (Suc m))"}, "next_step": {"operation": "have", "thought": "This fact implies 2 divides the product", "statement": {"english": "2 divides (n - 1) · n · (n + 1)", "isabelle": "2 dvd (n - 1) * n * (n + 1)"}, "next_step": ...}}}}

### Example
Assume the proof goal is $i > k > 1 \longrightarrow i^2 > k^2$
### English Proof
Induct on integer i, from 2 to positive infinity
### Formalized Proof
{"operation": "induction", "thought": "perform induction on the integer i, starting from 2", "target_isabelle_term": "i", "rule": {"rule": "increase", "from": "2"}, "variables": [{"name": "k", "varying": false}]}

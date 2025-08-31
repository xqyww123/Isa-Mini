You are an expert in Isabelle/HOL.
You are given an Isabelle proof context including proof goals, local variables, and local facts that serve as premises.
Your task is to apply operations described as follows, to reduce the goal or decompose it into simpler subgoals, step by step, to make it easier and to finally prove it.

All terms in goals and facts must be written in Isabelle/HOL.

## Operations
The operations fall into five sorts:
1. Reduction operations
- `SIMPLIFY`, for simplifying proof goals
- `UNFOLD`, for unfolding definitions
- `WITNESS`, for indicating the witness of existential quantification goals
- `RULE`, for reducing the proof goal by an indicated reasoning rule
- `CASE_SPLIT`, for case analysis
- `INDUCT`, for induction
- `BRANCH`, for splitting the proof case-by-case

2.  Decomposition operations:
- `HAVE`, for declaring subgoals
- `OBTAIN`, for obtaining variables satisfying certain conditions, one their existence are shown

3. `RETRIEVE` operation that retrieve facts from the system's knowledge base.

4. `ROLLBACK` operation that reverts to a previous proof state so you can try different proof operations in case you find the previous operations are ineffective and want to fix them.

5. Finally, `ATP` concludes simple proof goals by using Automated Theorem Provers.

Essentially, your task is to reduce or decompose the proof goal into simpler subgoals and finally conclude each of the subgoals by the `ATP` operation. The reduced subgoals must be simple enough in order to be accepted by `ATP` operation.

### Convention

#### Unicde
You must use Unicode instead of Isabelle's ASCII encoding in your output.

##### Example
Correct: "α ⇒ β"
Wrong: "\<alpha> \<Rightarrow> \<beta>"
Correct: "∀x. P x ⟹ ∃y. Q y"
Wrong: "\<forall>x. P x \<Longrightarrow> \<exists>y. Q y"
Correct: "[X₀, X₁, X⁰, X⁺, X₋, X₁₂]"
Wrong: "[X\<^sub>0, X\<^sub>1, X\<^sup>0, X\<^sup>+, X\<^sub>-, X\<^sub>1\<^sub>2]"

## Details of the Operations

### RETRIEVE
`RETRIEVE` searches the system knowledge base for relevant facts using pattern and name matching.

The local facts may not provide all the information needed to prove a goal, while a vast set of facts exists in the system's knowledge base. `RETRIEVE` allows you to retrieve facts that serve as relevant lemmas which greatly help your proof, when you feel the presented facts in the context are insufficient for the proof. Furthermore, the retrieved facts can also help you to understand constants when you are uncertain about their meaning.
You need to retrieve facts 

As follows, examples show how to use the pattern matching and the name matching.
```
function calling {
	"name": "RETRIEVE",
	"arguments": {"patterns": ["?listA ! ?i = ?listB ! ?i"]}
}

This calling retrieves 7 facts:
- List.nth_take: ?i < ?n ⟹ take ?n ?xs ! ?i = ?xs ! ?i
- List.nth_butlast: ?n < length (butlast ?xs) ⟹ butlast ?xs ! ?n = ?xs ! ?n
- List.nth_list_update_neq: ?i ≠ ?j ⟹ ?xs[?i := ?x] ! ?j = ?xs ! ?j
- List.takeWhile_nth: ?j < length (takeWhile ?P ?xs) ⟹ takeWhile ?P ?xs ! ?j = ?xs ! ?j
- List.list_eq_iff_nth_eq: (?xs = ?ys) = (length ?xs = length ?ys ∧ (∀i<length ?xs. ?xs ! i = ?ys ! i))
- List.nth_equalityI: length ?xs = length ?ys ⟹ (⋀i. i < length ?xs ⟹ ?xs ! i = ?ys ! i) ⟹ ?xs = ?ys
- List.nth_take_lemma: ?k ≤ length ?xs ⟹ ?k ≤ length ?ys ⟹ (⋀i. i < ?k ⟶ ?xs ! i = ?ys ! i) ⟹ take ?k ?xs = take ?k ?ys
```
Variables starting with qeustion makrs `?`, e.g.  `?var`, are free variables that can match any term.

Specially, `_` is an anonymous free variable, e.g.,
```
function calling {
	"name": "RETRIEVE",
	"arguments": {"patterns": ["card _ = _"]}
}
is equivalent to
function calling {
	"name": "RETRIEVE",
	"arguments": {"patterns": ["card ?x1 = ?x2"]}
}
```

You can set the pattern to a single constant to retrieve its definition and all facts related to the constant, which may help you to understand the constant:
```
function calling {
	"name": "RETRIEVE",
	"arguments": {"patterns": ["replicate"]}
}

This calling returns the definition of `replicate`:
  primrec replicate :: "nat ⇒ 'a ⇒ 'a list" where
  replicate_0: "replicate 0 x = []" |
  replicate_Suc: "replicate (Suc n) x = x # replicate n x"

The calling retrieves 54 facts (5 displayed):
- List.replicate.replicate_0: replicate 0 ?x = []
- List.linorder_class.sorted_replicate: sorted (replicate ?n ?x)
- List.length_replicate: length (replicate ?n ?x) = ?n
- List.concat_replicate_trivial: concat (replicate ?i []) = []
- List.replicate_transfer: rel_fun (=) (rel_fun ?A (list_all2 ?A)) replicate replicate
```
When too many facts are retrieved, only some of them are displayed. You may refine your query to narrow down the results.

If multiple patterns are provided, the retrieval returns facts that match BOTH of the patterns.
You must submit multiple callings if you want to retrieve facts matching EITHER of the patterns.

By providing negative patterns, the retrieval filters out all facts that match any negative pattern, e.g.,
```
function calling {
	"name": "RETRIEVE",
	"arguments": {"patterns": ["?listA ! ?i = ?listB ! ?i"], "negative patterns": ["take", "?i < ?n"]}
}
Facts that either contain constant `take` or match pattern `?i < ?n` are removed from the results.
```

Additionally, you can search for facts whose names contain indicated substrings:
```
function calling {
	"name": "RETRIEVE",
	"arguments": {"patterns": ["card _ = _"], "names": ["List"]}
}
This calling constrains that the fact names must contain "List", which is a way to constrain the facts within the List related theories.

The calling returns:
- List.card_set: card (set ?xs) = length (remdups ?xs)
- List.distinct_card: distinct ?xs ⟹ card (set ?xs) = length ?xs
- List.card_distinct: card (set ?xs) = length ?xs ⟹ distinct ?xs
...
```

### SIMPLIFY
`SIMPLIFY` simplifies the proof goal and some recent local facts.
Generally for most of proof goals, this is the first operation you should apply before any other operation.

You should especially apply `SIMPLIFY` when the proof goal contains reducible terms such as `[1,2] @ [4]`, `rev [1,2]`, or `23 + 3`. Example:
```
Given a proof context:
VARIABLES:
- P : nat ⇒ bool
GOAL: P (1 + 2)

function calling {
	"name": "SIMPLIFY",
	"arguments": {}
} reduces the context to:

VARIABLES:
- P : nat ⇒ bool
GOAL: P 3
```

`SIMPLIFY` accepts additional simplification rules. You can add definitions as simplification rules to unfold these definitions. Example:
```
Given a proof context:
FACTS:
- prefix_def: prefix ?xs ?ys = (∃zs. ?ys = ?xs @ zs)
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ps : 'a list
- qs : 'a list
LOCAL FACTS:
- fact0: prefix ps xs
- fact1: prefix qs xs
- fact2: length ps ≤ length qs
GOAL: prefix ps qs

function calling {
	"name": "SIMPLIFY",
	"arguments": {"rules": ["prefix_def"]}
} reduces the context to:

TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ps : 'a list
- qs : 'a list
- zs : 'a list
- zsa : 'a list
LOCAL FACTS:
- fact0: length ps ≤ length qs
- fact1: xs = qs @ zsa
- fact2: ps @ zs = qs @ zsa
GOAL: ∃zs. qs = ps @ zs
```

`SIMPLIFY` simplifies all the recent local facts until either `HAVE`, `CONSIDER`, or `BRANCH` is applied. Once one of the operations is applied, all existing local facts are freezed.

### UNFOLD
`SIMPLIFY` with definitions as its arguments is sufficient for unfolding definitions. However, if you want to indicate the constants to unfold instead of their definitional facts, you can use `UNFOLD` with the names of the constants as the arguments.

Example:
```
Given a proof context:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- y : 'a
- xs : 'a list
- ys : 'a list
LOCAL FACTS: empty
GOAL: suffix xs (y # ys) ⟷ xs = y # ys ∨ suffix xs ys

function calling {
	"name": "UNFOLD",
	"arguments": {"targets": ["suffix"]}
} reduces the context to:

TYPE VARIABLES:
- 'a : type
VARIABLES:
- y : 'a
- xs : 'a list
- ys : 'a list
LOCAL FACTS: empty
GOAL: (∃zs. y # ys = zs @ xs) = (xs = y # ys ∨ (∃zs. ys = zs @ xs))
```

### WITNESS
`WITNESS` instantiates witnesses of existential quantifications in the proof goal. For example,
```
Given a proof context:
TYPE VARIABLES:
- 'a : type
- 'b : type
VARIABLES:
- f : 'b ⇒ 'a
- xs : 'a list
- ys : 'b list
- n : nat
LOCAL FACTS:
- fact0: map f ys = xs' @ xs
- fact1: n = length xs'
- fact2: xs = drop n (map f ys)
GOAL: ∃xs'. suffix xs' ys ∧ xs = map f xs'

function calling {
	"name": "WITNESS",
	"arguments": {"witnesses": ["drop n ys"]}
} reduces the context to:

TYPE VARIABLES:
- 'a : type
- 'b : type
VARIABLES:
- f : 'b ⇒ 'a
- xs : 'a list
- ys : 'b list
- n : nat
LOCAL FACTS:
- fact0: map f ys = xs' @ xs
- fact1: n = length xs'
- fact2: xs = drop n (map f ys)
GOAL: suffix (drop n ys) ys ∧ xs = map f (drop n ys)
```

`WITNESS` is available only when an existential quantification is the leading connective of the goal.

When the goal has more than one existential quantifications, `WITNESS` accepts corresponding multiple witenesses to instantiate the quantifications in a single call, e.g.,
```
Given a proof context:
TYPE VARIABLES: empty
VARIABLES: empty
LOCAL FACTS: empty
GOAL: ∃n k. 7 = 3 * n + k

function calling {
	"name": "WITNESS",
	"arguments": {"witnesses": ["2", "1"]}
} reduces the context to:

TYPE VARIABLES: empty
VARIABLES: empty
LOCAL FACTS: empty
GOAL: 7 = 3 * 2 + 1
```

### RULE
Sometimes, it is helpful to reduce the proof goal into simpler subgoals following a predefined reasoning rule.  For example, goal `A ⟷ B` can be reduced to subgoals `A ⟶ B` and `B ⟶ A`, by the default rule of `⟷`. This reduction by rule is realized by operation `RULE`:
```
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
LOCAL FACTS: empty
GOAL: suffix xs ys ⟶  prefix (rev xs) (rev ys)

function calling {
	"name": "RULE",
	"arguments": {}
}
This calling reduces the goal into two subgoals.

The first subgoal is
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
LOCAL FACTS:
- fact0: suffix xs ys
GOAL: prefix (rev xs) (rev ys)

The second subgoal is
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
LOCAL FACTS:
- fact0: prefix (rev xs) (rev ys)
GOAL: suffix xs ys
```

By setting the optional argument `rule`, you can also indicate the reasoning rule to apply if it is not the default. Example:
```
FACT:
- bij_betw_same_card: bij_betw ?f ?A ?B ⟹ card ?A = card ?B

TYPE VARIABLES:
- 'a : ab_group_add
VARIABLES:
- A : 'a set
LOCAL FACTS: empty
GOAL: card (A + {a}) = card A

function calling {
	"name": "RULE",
	"arguments": {"rule": "bij_betw_same_card"}
}
The calling reduces the goal into

TYPE VARIABLES:
- 'a : ab_group_add
VARIABLES:
- A : 'a set
- ?f : 'a ⇒ 'a
LOCAL FACTS: empty
GOAL: bij_betw ?f (A + {a}) A
```


### CASE_SPLIT
`CASE_SPLIT` applies structural case analysis over an indicated term.
For example, case analysis over a list splits the proof goal into the case for an empty list and the case for the list constructor `Cons`:
```
Given a proof context:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- y : 'a
- xs : 'a list
- ys : 'a list
LOCAL FACTS: empty
GOAL: prefix xs (y # ys) = (xs = [] ∨ (∃zs. xs = y # zs ∧ prefix zs ys))

function calling {
	"name": "CASE_SPLIT",
	"arguments": {"target": ["xs"]}
} generates two sub goals.

The first subgoal is:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- y : 'a
- xs : 'a list
- ys : 'a list
LOCAL FACTS:
- fact0: xs = []
GOAL: prefix [] (y # ys) = ([] = [] ∨ (∃zs. [] = y # zs ∧ prefix zs ys))

The second subgoal is:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- y : 'a
- xs : 'a list
- ys : 'a list
- a : 'a
- list : 'a list
LOCAL FACTS:
- fact0: xs = a # list
GOAL: prefix (a # list) (y # ys) = (xs = [] ∨ (∃zs. a # list = y # zs ∧ prefix zs ys))
```

### INDUCT
`INDUCT` applies induction over an indicated term. This term can be a natural number, a list, or any other recursive datatype.

Examples:
```
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
- zs : 'a list
LOCAL FACTS: empty
GOAL: prefix (xs @ ys) (xs @ zs) = prefix ys zs

function calling {
	"name": "INDUCT",
	"arguments": {"target": "xs"}
}
The calling produces two subgoals, the case when "xs = []" and the case when "xs = a # xs'". The `#` symbol represents list construction.

The first subgoal:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- ys : 'a list
- zs : 'a list
LOCAL FACTS: empty
GOAL: prefix ([] @ ys) ([] @ zs) = prefix ys zs

The second subgoal:
TYPE VARIABLES: empty
- 'a : type
VARIABLES:
- a : 'a
- ys : 'a list
- xs' : 'a list
- zs : 'a list
LOCAL FACTS:
- fact0: prefix (xs' @ ys) (xs' @ zs) = prefix ys zs
GOAL: prefix ((a # xs') @ ys) ((a # xs') @ zs) = prefix ys zs
```

By default, the `INDUCT` operation leaves all variables other than the induction target untouched, maintaining their original bindings across all inductive cases. However, this often makes the induction hypothesis too weak to complete the proof, because you often need to instantiate the variables differently in the inductive hypotheses than they appear in the goal. One way to address this is to universally re-quantify these variables in the hypotheses, yielding stronger induction hypotheses where you can instantiate the variables arbitrarily. To do so, specify the variables as `arbitrary` parameters, e.g.,
```
TYPE VARIABLES:
- 'a : type
VARIABLES:
- S : 'a set
- n : nat
LOCAL FACTS:
- fact0: infinite S
GOAL: enumerate S n ∈ S

function calling {
	"name": "INDUCT",
	"arguments": {"target": "n", "arbitrary": ["S"]}
}
The calling produces two subgoals, the case for "n = 0" and the case for "n = Suc n'" for some "n'"

The first subgoal:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- S : 'a set
LOCAL FACTS:
- fact0: infinite S
GOAL: wellorder_class.enumerate S 0 ∈ S

The second subgoal:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- S : 'a set
- n' : nat
LOCAL FACTS:
- fact0: ⋀S. infinite S ⟹ wellorder_class.enumerate S n' ∈ S
- fact1: infinite S
GOAL: wellorder_class.enumerate S (Suc n') ∈ S

By contrast, the function calling {
	"name": "INDUCT",
	"arguments": {"target": "n"}
} without setting the arbitrary parameter produces the following two subgoals.

The first subgoal is the same as the above one.

The second subgoal:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- S : 'a set
- n' : nat
LOCAL FACTS:
- fact0: infinite S ⟹ wellorder_class.enumerate S n' ∈ S
- fact1: infinite S
GOAL: wellorder_class.enumerate S (Suc n') ∈ S

The key difference is that the S in the fact0 is bound to the S in the goal, while in the version with the arbitrary argument, they are independent.
```
Forgetting setting variables as arbitrary, is a common reason causing a proof failure. It is often to frequently apply `ROLLBACK` operation to revise a weak induction by adding missing arbitrary arguments.

You can also indicate an induction rule to fine-control the induction. For example, induct over a list reversely from its tail instead of from its head as usual:
```
FACTS:
- rev_induct: ?P [] ⟹ (⋀x xs. ?P xs ⟹ ?P (xs @ [x])) ⟹ ?P ?xs

TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
- zs : 'a list
LOCAL FACTS: empty
GOAL: prefix xs (ys @ zs) = (prefix xs ys ∨ (∃us. xs = ys @ us ∧ prefix us zs))

function calling {
	"name": "INDUCT",
	"arguments": {"target": "zs", "rule": "rev_induct"}
}
The calling produces two subgoals, the case for "zs = []" and the case for "zs = zs' @ [a]" for some zs' and a

The first subgoal:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
LOCAL FACTS: empty
GOAL: prefix xs (ys @ []) = (prefix xs ys ∨ (∃us. xs = ys @ us ∧ prefix us []))

The second subgoal:
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
- zs : 'a list
- a : 'a
LOCAL FACTS:
- fact0: prefix xs (ys @ zs) = (prefix xs ys ∨ (∃us. xs = ys @ us ∧ prefix us zs)) ⟹
GOAL: prefix xs (ys @ zs @ [a]) = (prefix xs ys ∨ (∃us. xs = ys @ us ∧ prefix us (zs @ [a])))
```

### ATP
`ATP` applies Automated Theorem Provers (ATPs) to prove the goal. However, the capability of the ATPs is limited and cannot handle difficult problems. This difficulty refers to the computational complexity or reasoning depth needed to solve the problem, rather than the syntactic length of the goal terms. Many long goals involving complicated terms can be effectively proven.

`ATP` is the last step to prove a goal. You should apply `ATP` if and only if you think the goal is simple enough to be handled by ATPs.
Typically you should reduce or decompose a proof goal using other operations into simpler subgoals, and finally apply `ATP` to conclude these goals.

Example:
```
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
LOCAL FACTS:
- fact0: prefix xs ys
- fact1: sorted ys
GOAL: sorted xs

function calling {
	"name": "ATP",
	"arguments": {}
}

The goal is proven.
```

It can effectively boost `ATP` if you indicate additional lemmas to use, by setting the `lemmas` parameter.

### BRANCH
`BRANCH` splits the proof goal into indicated cases. For example,
```
TYPE VARIABLES: empty
VARIABLES:
- x : int
- y : int
LOCAL FACTS:
- fact0: omited
- fact1: omited
GOAL: ∃u v. u * x + v * y = gcd x y 

function calling {
	"name": "BRANCH",
	"arguments": {"cases": [["x ≥ 0" "y ≥ 0"], ["x ≥ 0" "y ≤ 0"], ["x ≤ 0" "y ≥ 0"], ["x ≤ 0" "y ≤ 0"]]}
}
This calling splits the proof into four cases:
1. x ≥ 0 ∧ y ≥ 0
2. x ≥ 0 ∧ y ≤ 0
3. x ≤ 0 ∧ y ≥ 0
4. x ≤ 0 ∧ y ≤ 0
However, five subgoals are produced.

As the first subgoal, you have to show that these cases cover all possibilities, i.e., it can only be one of these cases, and no other possibilities exist.
The first subgoal is,
TYPE VARIABLES: empty
VARIABLES:
- x : int
- y : int
LOCAL FACTS:
- fact0: omited
- fact1: omited
GOAL: (x ≥ 0 ∧ y ≥ 0) ∨ (x ≥ 0 ∧ y ≤ 0) ∨ (x ≤ 0 ∧ y ≥ 0) ∨ (x ≤ 0 ∧ y ≤ 0)

The second subgoal corresponds to the first case ("x ≥ 0" "y ≥ 0"),
TYPE VARIABLES: empty
VARIABLES:
- x : int
- y : int
LOCAL FACTS:
- fact0: omited
- fact1: omited
- fact2: "x ≥ 0"
- fact3: "y ≥ 0"]
GOAL: ∃u v. u * x + v * y = gcd x y 

The third subgoal corresponds to the second case ("x ≥ 0" "y ≤ 0"),
TYPE VARIABLES: empty
VARIABLES:
- x : int
- y : int
LOCAL FACTS:
- fact0: omited
- fact1: omited
- fact2: "x ≥ 0"
- fact3: "y ≤ 0"]
GOAL: ∃u v. u * x + v * y = gcd x y 

The remaining subgoals correspond similarly to the remaining cases. They are omitted.
```

### HAVE
`HAVE` introduces a sequence of subgoals. It suspends the current proof and shifts to proving the subgoals. Once these subgoals are proven, the proof of the original goal is resumed, and the proven subgoals become available as lemmas for use in the proof of the original goal.

 `HAVE` allows you to break down a proof goal by first establishing a sequence of intermediate lemmas. After proving these intermediate subgoals, you can reference them as proven lemmas while constructing the proof of your main goal.

Example
```
FACT:
- Discrete.sqrt_def: Discrete.sqrt n = Max {m. m² ≤ n}

VARIABLES:
- n : nat
LOCAL FACTS: empty
GOAL: Discrete.sqrt (n²) = n

function calling {
	"name": "HAVE",
	"arguments": [
		"{m. m ≤ n} ≠ {}",
		"Max {m. m ≤ n} ≤ n"
	]
}
This calling introduces two new subgoals, and augments the original goal with the proofs of the two subgoals. Thus, including the original goal, there are three subgoals in total.

The first subgoal is,
VARIABLES:
- n : nat
LOCAL FACTS: empty
GOAL: {m. m ≤ n} ≠ {}

The second subgoal is,
VARIABLES:
- n : nat
LOCAL FACTS:
- fact0: {m. m ≤ n} ≠ {}
GOAL: Max {m. m ≤ n} ≤ n

The third subgoal is the augmented original goal,
VARIABLES:
- n : nat
LOCAL FACTS:
- fact0: {m. m ≤ n} ≠ {}
- fact1: Max {m. m ≤ n} ≤ n
GOAL: Discrete.sqrt (n²) = n
```

### OBTAIN
`OBTAIN` extracts witnesses from existential statements and introduces fresh variables to bind them. This enables the proof step "let x be such that P(x)" once you've established "there exists x such that P(x)". 

For example, once you show `∃j k. m = j * n + k`, `OBTAIN` introduces two fresh local variables `j, k` and one local fact `m = j * n + k`. The function calling for this example is `{"name": "OBTAIN", "arguments": {"variables": ["j","k"], "conditions": ["m = j * n + k"]}}`

Example:
```
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
LOCAL FACTS:
- fact0: suffix xs ys
GOAL: prefix (rev xs) (rev ys)

function calling {
	"name": "OBTAIN",
	"arguments": {"variables": ["zs"], "conditions": ["ys = zs @ xs"]}
}
The calling yields two subgoals.

As the first subgoal, you need to show the existence of such zs.
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
LOCAL FACTS:
- fact0: suffix xs ys
GOAL: ∃zs. ys = zs @ xs

The second subgoal is the original goal augmented with zs and its condition.
TYPE VARIABLES:
- 'a : type
VARIABLES:
- xs : 'a list
- ys : 'a list
- zs : 'a list
LOCAL FACTS:
- fact0: suffix xs ys
- fact1: ys = zs @ xs
GOAL: prefix (rev xs) (rev ys)
```

### ROLLBACK
`ROLLBACK` rollbacks the proof state back to a previous state, so that you can revise and reapply previous proof operations.
Specifically, each proof state is assigned with an index and each operation application increases the index by one.

## Now Let's Start the Proof Task
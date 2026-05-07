1.
```
variables:
  - Q: 'c ⇒ 'a ⇒ bool
  - P: 'b ⇒ 'a ⇒ bool
  - R: 'a ⇒ bool
You could add global declarations here.
goal: ∀a. R a ⟶ (∀b. P b a) = (∀c. Q c a)
proof:
  - step id: 1
    operation: Intro
    fixing variables:
      - a: 'a
    assuming premises:
      - premise0: R a
  - step id: 2
    thought: Destruct equivalence
    operation: Proof by inference rule
    rule: default # 这里最好能替换成具体所使用的 rule
    derived subgoals:
      - goal id: 2.1
        goal: (∀b. P b a) ⟶ (∀c. Q c a)
        proof:
          - step id: 2.1.1
            operation: Intro
            fixing variables:
              - c: 'c
            assuming premises:
              - premise1: ∀b. P b a
        Error: Unfinished Proof! Call command `edit` with action `fill` and target step `2.1.2` to provide the proof for the following goal.
        pending proof goal:
          goal: Q c a
      - goal id: 2.2
        goal: (∀c. Q c a) ⟶ (∀b. P b a)
        proof:
          - step id: 2.2.1
            operation: Intro
            fixing variables:
              - b: 'b
            assuming premises:
              - premise2: ∀c. Q c a
        Error: Unfinished Proof! Call command `edit` with action `fill` and target step `2.2.2` to provide the proof for the following goal.
        pending proof goal:
          goal: P b a
```

2. 实现 Tactic Opr Node：用 semantic embedding 来实现调用任何 tactics with arbitrary arguments


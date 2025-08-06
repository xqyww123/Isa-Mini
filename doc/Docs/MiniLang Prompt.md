MiniLang is an alternative proof language for Isabelle/HOL. We use MiniLang to prove formal statement under a given context. Please strictly follow the commands and syntax defined below when generating your answer.

# MiniLang Syntax

## Comment

Any comment must be surrounded by (* and *) 
### Example
(* this is a comment *)

## Unicode

You must use Unicode instead of Isabelle's ASCII encoding in your output.

### Example

Correct: "α ⇒ β"
Wrong: "\<alpha> \<Rightarrow> \<beta>"
Correct: ∀x. P x ⟹ ∃y. Q y
Wrong: "\<forall>x. P x \<Longrightarrow> \<exists>y. Q y"
Correct: "[X₀, X₁, X⁰, X⁺, X₋, X₁₂]"
Wrong: "[X\<^sub>0, X\<^sub>1, X\<^sup>0, X\<^sup>+, X\<^sub>-, X\<^sub>1\<^sub>2]"

## Type Annotation
All digits, variables must be annotated with their types
### Example
Correct: " (1::real)/(2::real) + (2::real)/(3::real) = (7::real)/(6::real) "
Correct: " (1::int)/(2::int) + (2::int)/(3::int) = (7::int)/(6::int) "
Wrong: " 1/2 + 2/3 = 7/6 "
Correct: " ∑ (k::nat) ∈ {1..<n}. k "
Wrong: " ∑ k ∈ {1..<n}. k "
Correct: "∀(x::nat) . ∃(y::nat) . x < y "
Wrong: "∀x. ∃y. x < y "

# MiniLang Commands
## Have
Usage: introduces lemma, useful for splitting a goal into smaller subgoals.
### Example
Have name: "statement"
(* proofs for statement *)
End
### Example
Goal "rev (a @ rev (b @ c)) = b @ c @ a"
Have step1: "rev (b @ c) = c @ b" End
Have step2: "rev (a @ (c @ b)) = b @ c @ a" End
End
## Consider
Usage 1: proof by cases.
### Example
Goal "G"
Consider "x < (0::int)" | "x = (0::int)" | "x > (0::int)"
(* prove these cases are exhaustive *)
Next
(* prove G  when x < 0 *)
Next
(* prove G  when x = 0 *)
Next
(* prove G  when x > 0 *)
End
Usage 2: introduces witness of existential quantification.
Example: Consider x where P(x) (* let x be such that P(x) holds. *)
## Cases
Usage: case analysis on terms according to their constructors
### Example
Goal "length (tl xs) = length xs - (1::nat)"
Cases "xs"
(* yields two cases: "xs = [] " and " xs = x # xs' " for certain x, xs' *)
(* prove the goal when xs = [] *)
Next
(* prove the goal when xs = x # xs' *)
End

## Induction
Usage: induction over a term.
### Example
Goal "rev (rev l) = l"
Induction "l"
(* Prove the base case, where l = [] *)
Next
(* Prove the induction step, where l = x # l' for certain x, l' *)
End

## Define
Usage: introduce a definition
### Example
Define split_list where "split_list l n = (take n l, drop n l)"

## End
Usage: concludes a proven goal or skips a simple goal.
### Example
Goal " (1::nat) + (1::nat) = (2::nat) "
End
## Next
Usage: concludes the first goal and turns to the next goal. 


## Example
### Goal
variable x::real
assumption "0<x" "x<pi"
Goal "(12::real) ≤ ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"
### Proof
Define y where "y=x * sin x"
Have fact1: "(12::real) ≤ ( (9::real) * (y::real) ^ (2::nat) + (4::real) ) / y"
(* fact2 and fact3 are only visible in the proof of fact1 *)
Have fact2: "y > (0::real) " End
Have fact3: "(0::real) ≤ (This is your new *vault*.

Make a note of something, [[create a link]], or try [the Importer](https://help.obsidian.md/Plugins/Importer)￼!

When you're ready, delete this note and make the vault your own. (3::real) * y - (2::real) ) ^ (2::nat)" End
End
End

## Example
### Goal
variable x::real
assumption "(0::real) < x" " x < pi "
Goal " (12::real) ≤ (( (9::real) * ( x^(2::nat) * (sin x)^(2::nat) )) + (4::nat)) / (x * sin x)"
### Proof
Define y where "y=x * sin x"
(* fact1, fact2 and fact3 are all visible in the proof of the goal *)
Have fact1: "(12::real) ≤ ((9::real) * y^(2::nat) + (4::real)) / y"
Have fact2: "y > (0::real)" End
Have fact3: "(0::real) ≤ ( (3::real) * (y::real) - (2::real) ) ^ (2::nat)" End
End
End

## Example

### Goal
variable x :: real
assumption "x \<noteq> 0"
Goal "1/(4/x) * ((3*x^3)/x)^2 * (1/(1 / (2 * x)))^3 = 18 * x^8"

### Proof
  Have "1/(4/x) = x/4" End
  Have "(3*x^3)/x=3*x^2" End
  Have "3*x^3)/x)^2 = (3*x^2)^2" End
  Have "(3*x^2)^2 = 9 * x^4" End
  Have "((3*x^3)/x)^2 = 9 * x^4" End
  Have "(1/(1 / (2 * x)))^3 = (2*x)^3" End
  Have "(2*x)^3 = 8 * x^3" End
  Have "(1/(1 / (2 * x)))^3 = 8 * x^3" End
  Have "1/(4/x) * ((3*x^3)/x)^2 * (1/(1 / (2 * x)))^3 = x/4 * (9 * x^4) * (8 * x^3)" End
  Have "(9 * x^4) * (8 * x^3) = 9 * 8 * x^4 * x^3" End
  Have "9 * 8 * x^4 * x^3 = 72 * x^7" End
  Have h6: "(9 * x^4) * (8 * x^3) = 72 * x^7" End
  Have "x/4 * (9 * x^4) * (8 * x^3) = x/4 * 72 * x^7" End
  Have "x/4 * 72 * x^7 = 18 * x * x^7" End
  Have "18 * x * x^7 = 18 * x^1 * x^7" End
  End

## Example
### Goal
variable f :: 'b ⇒ 'a and xs :: 'b list and g :: 'c ⇒ 'a
assumption "map f xs = map g ys"
Goal "length xs = length ys"
### Proof
Induction ys arbitrary: xs with assumption
(* The base case is trivial *)
Next variable y ys'
(* The inductive step: xs = x xs' *)
Consider z zs where " xs = z # zs " End
Have " map f zs = map g xs' " End
Have " length zs = length xs' " End
End

## Example


## Your Task
Strictly using MiniLang, prove the following statement
### Goal
Goal "sqrt (2::real) ∉ ℚ"


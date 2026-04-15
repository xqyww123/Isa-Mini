---
name: isabelle-fun-definition
description: How to write correct recursive function definitions with the Define operation
---

# Recursive Function Definitions

Split cases using multiple equations with constructor patterns. Each equation's left-hand side must be specific enough that it cannot match a recursive call on the right-hand side — otherwise Isabelle's simplifier loops.

## Bad → Good

### nat

Bad:
```
equations: ["f n = (if n = 0 then 0 else 1 + f (n - 1))"]
```
Good:
```
equations: ["f 0 = 0", "f (Suc n) = Suc (f n)"]
```

### list

Bad:
```
equations: ["len xs = (if xs = [] then 0 else 1 + len (tl xs))"]
```
Good:
```
equations: ["len [] = 0", "len (x # xs) = 1 + len xs"]
```

### Multiple arguments

Bad:
```
equations: ["zs a b n = (if n = 0 then 0 else if n < b then b + zs 1 2 (n - a) else zs b (a + b) n)"]
```
Good:
```
equations: ["zs a b 0 = 0", "zs a b (Suc n) = (if Suc n < b then b + zs 1 2 (n - a + 1) else zs b (a + b) (Suc n))"]
```

### Pairs / tuples

Bad:
```
equations: ["f p = (if fst p = 0 then snd p else f (fst p - 1, snd p + 1))"]
```
Good:
```
equations: ["f (0, m) = m", "f (Suc n, m) = f (n, m + 1)"]
```

## Constructor Patterns

| Type | Constructors |
|------|-------------|
| `nat` | `0`, `Suc n` |
| `'a list` | `[]`, `x # xs` |
| `'a option` | `None`, `Some x` |
| `bool` | `True`, `False` |
| `'a * 'b` | `(a, b)` |

## When `if` is OK

`if` in the RHS is fine when the LHS already has constructor patterns that prevent self-matching:

```
equations:
  - "merge [] ys = ys"
  - "merge xs [] = xs"
  - "merge (x # xs) (y # ys) = (if x \<le> y then x # merge xs (y # ys) else y # merge (x # xs) ys)"
```

The LHS `merge (x # xs) (y # ys)` cannot match the recursive calls `merge xs (y # ys)` or `merge (x # xs) ys` because `xs` is not `_ # _` and `ys` is not `_ # _`.

## Metric

When Isabelle cannot prove termination automatically, supply a `metric`:

```json
{
  "operation": "Define",
  "name": "halve",
  "type": "nat \u21d2 nat",
  "equations": ["halve 0 = 0", "halve (Suc 0) = 0", "halve (Suc (Suc n)) = Suc (halve n)"],
  "metric": ["\u03bbn::nat. n"]
}
```

A metric is a function from the argument types (as a tuple) to `nat` that strictly decreases on each recursive call.

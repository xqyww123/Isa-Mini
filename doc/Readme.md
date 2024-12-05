Isa Proof Shell
====

A streamlined, Unix-pipeline-based shell for Isabelle's proof system, optimized for integration between Isabelle and machine learning systems.
This shell offers a minimal language and abstraction layer that eliminates human-oriented complexities in Isabelle, making it particularly suitable for AI agents.

> The development currently works in progress. We welcome suggestions, feature requests, and concerns through GitHub issues.

## Key Features

- **Communication**: Text-based standard I/O with JSON format
- **Minimized Interface**: Minimal number of commands integrating powerful automation tools like Sledgehammer
- **Concurrency**: Efficient concurrent proof sessions powered by Isabelle's built-in thread scheduler
- **State Management**: Support for restore historical proof states.
- **Bidirectional Portal**: That also eases Isabelle to call AI agents in future.
	- A shell script that successfully proves a goal, also produces an Isabelle tactic script able to reproduce the proof without using the shell.
## Motivation

Isabelle/HOL has evolved into a sophisticated system with numerous features optimized for human interaction. While powerful, many of these features—such as the human-readable Isar language—are unnecessary overhead when working with AI agents. This shell aims to:

1. Strip away non-essential elements and provide a minimal, agent-friendly interface
2. Integrate existing automation mechanisms

### Example of Simplification

The current Isabelle system includes:

- Numerous Isar commands (`have`, `moreover`, `ultimately`, `obtain`, `hence`, `thus`, `show`, `shows`, `assume`, `assumes`, `lemma`, `theorem`, `corollary`, `by`, `apply`, `done`, `qed`, `proof`, etc.)
- Multiple subsystems (attributes, tactics, documentation, modules)
- Various tactics (`this`, `rule`, `erule`, `drule`, `subst`, `simp`, `auto`, `linarith`, `blast`, `fast`, `fastforce`, `force`, `smt`, `metis`, `meson`)

Many of these commands and tactics have subtle differences and overlapping functionality. Our shell reduces this complexity to fewer than 10 essential proof commands (see [Language Reference](/doc/Language%20and%20Protocol.md) for details).

As an example, take the proof for "the square root of two is irrational" given in [the Wikipedia page of Isabelle](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant))
```isabelle
theorem sqrt2_not_rational:
  "sqrt 2 ∉ ℚ"
proof
  let ?x = "sqrt 2"
  assume "?x ∈ ℚ"
  then obtain m n :: nat where
    sqrt_rat: "¦?x¦ = m / n" and lowest_terms: "coprime m n"
    by (rule Rats_abs_nat_div_natE)
  hence "m^2 = ?x^2 * n^2" by (auto simp add: power2_eq_square)
  hence eq: "m^2 = 2 * n^2" using of_nat_eq_iff power2_eq_square by fastforce
  hence "2 dvd m^2" by simp
  hence "2 dvd m" by simp
  have "2 dvd n" proof -
    from ‹2 dvd m› obtain k where "m = 2 * k" ..
    with eq have "2 * n^2 = 2^2 * k^2" by simp
    hence "2 dvd n^2" by simp
    thus "2 dvd n" by simp
  qed
  with ‹2 dvd m› have "2 dvd gcd m n" by (rule gcd_greatest)
  with lowest_terms have "2 dvd 1" by simp
  thus False using odd_one by blast
qed
```
This proof is translated into our language as follows
```
GOAL "sqrt 2 ∉ ℚ"
    CRUSH
    LET ?x = "sqrt 2"
    OBTAIN m n :: nat where "¦?x¦ = m / n" and "coprime m n"; END
    HAVE "m^2 = ?x^2 * n^2"; END
    HAVE "m^2 = 2 * n^2"; END
    HAVE "2 dvd m^2"; END
    HAVE "2 dvd m"; END
    HAVE "2 dvd n"
        OBTAIN k where "m = 2 * k"; END
        HAVE "2 * n^2 = 2^2 * k^2"; END
    END
    HAVE "2 dvd gcd m n"; END
    HAVE "2 dvd 1"; END
    HAVE "False"; END
END
```
Our language is more concise because we use Sledgehammer to automatically generate every small proof script used in the original code. The idea is to let AI agents focus on the macroscopic proof route planning, and leave all the trivial small stuff to existing proof automation mechanisms like Sledgehammer. 

Clients just need to start up our shell, and send the above text through the standard input pipeline (`stdin`), and that is all required to prove lemmas using our shell. If the proof works, our shell shall return an Isabelle script allowing anyone to reproduce the proof.

## Schedule (Planned)

| Due Date         | Phase                       |
| ---------------- | --------------------------- |
| Week 1, November | Proposal Draft Release      |
| Week 4, November | Design Specification Freeze |
| Week 2, December | Alpha Release               |
| Week 4, December | Stable Release              |

## Design Specification (Draft)

- [Language and Protocol](/doc/Language%20and%20Protocol.md)

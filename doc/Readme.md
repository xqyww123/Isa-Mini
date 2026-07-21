Isabelle/Minilang
====

**A minimalist proof language for Isabelle/HOL, designed for machine learning and LLM agents.**

Minilang eliminates the human-oriented complexities of Isabelle/Isar, letting language models focus on high-level proof planning while delegating fine-grained reasoning to classical automation (Sledgehammer & friends). What started as a minimal proof shell has grown into a full stack:

- **Minilang** — a minimalist proof language with only ~10 core operations, each with clear semantic distinctions ([OOPSLA'26 paper](https://dl.acm.org/doi/10.1145/3798275))
- **Translator** — a rule-based Isar → Minilang translator that has converted ~85% of ~340K existing Isabelle/AFP proofs into a large-scale training corpus ([code](https://github.com/xqyww123/Isa-Mini-Translator))
- **AoA Agent** — *Agent over AST*: a token-efficient LLM proof agent that edits Minilang proofs directly as JSON abstract syntax trees, usable from inside Isabelle via a single `by aoa` method ([paper](https://arxiv.org/abs/2607.16372), [code](/IsaMini/AoA), [README](IsaMini/AoA/Readme.md))

Visit our [Example Gallery](https://docs.google.com/presentation/d/14VY5HkMRmOhRkKBvmISymKtNg5e650EZgzt-KajqMRI/edit?usp=sharing) to see more.

## Key Features

### AoA: Agent over AST

The AoA agent answers a practical question: *how do we cut the prohibitive API cost of LLM proof agents, and how do we let general-purpose LLMs write proofs in a language too new to appear in their training corpora?*

- **AST-native interaction**: instead of emitting source text and re-locating states by line numbers after every edit, the model supplies proofs as JSON representations of Minilang's AST — a format native to tool-calling LLMs — and drives the prover through a tree-edit model.
- **Proof tree = operations + states**: proof operations and proof states are fused into one tree, so each operation carries its own subgoal's state, readable directly off the tree without separate queries.
- **Token- and cost-efficient**: against Amazon's Isabelle Agent on the miniF2F and NTP4VC-Pearl common success sets, AoA cuts API cost by **2.3–4.7×**, uses **2.9–6.9× fewer tokens** and **3.9–8.9× fewer tool calls**, and finishes **1.4–2.0× faster** — while solving more problems on the harder verification benchmark.
- **No fine-tuning required**: works with general-purpose LLMs out of the box, with drivers for Claude Code, Codex, and OpenAI-compatible / Anthropic APIs.
- **One-line usage inside Isabelle**: invoke the agent on any goal simply with the proof method `by aoa`.

See the paper: [*Theorem-Proving Agent over Abstract Syntax Tree of Redesigned Language*](/doc/AoA.pdf).

### Proven effectiveness of Minilang for Neural Theorem Proving

Fine-tuning LLMs on the Minilang corpus (instead of raw Isar) improves the pass@1 success rate on the PISA benchmark by up to **20/29 percentage points** compared to Isar-based models with/without Sledgehammer:

- **pass@1 reaches 69.1%**, exceeding Baldur's pass@64 (65.7%)
- **pass@8 reaches 79.2%**, exceeding the previous SOTA on PISA (71.0%, Magnushammer)

See the paper: [*A Minimalist Proof Language for Neural Theorem Proving over Isabelle/HOL*](https://arxiv.org/abs/2507.18885).

### The corpus & translator

- Rule-based translation from Isar to Minilang via three strategies: *elaboration* (make implicit information explicit), *normalization* (consolidate diverse idioms into uniform representations), and *elimination of tactics* (replace tactics with Sledgehammer\*, except those matching informal reasoning).
- **~290K proofs** (85.25% of ~340K Isar proofs from Isabelle/AFP) successfully translated, forming one of the largest structured proof corpora for machine learning.


## Citation

If you use Minilang or this repository, please cite:

```bibtex
@misc{xu2025minilang,
  title={A Minimalist Proof Language for Neural Theorem Proving over Isabelle/HOL},
  author={Qiyuan Xu and Renxi Wang and Peixin Wang and Haonan Li and Conrad Watt},
  year={2025},
  eprint={2507.18885},
  archivePrefix={arXiv},
  primaryClass={cs.PL},
  url={https://arxiv.org/abs/2507.18885},
}
```

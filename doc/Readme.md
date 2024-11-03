This is an easy-to-use UNIX-pipeline-based shell of Isabelle's proof system, aiming to ease the difficulty of chaining Isabelle with machine learning training system.
This shell equips its own language, providing an abstraction layer wrapping and simplifying all the complex Isabelle components designed for humans, to specially please AI agents.

Due to design principles and sometimes historical burdens, Isabelle/HOL has evolved into a complex system. However, most of its features, such as the human-friendly and -readable Isar, are redundant for use and unnecessary for AI agents. This shell aims to rule out all the unnecessary elements, and also integrate powerful existing automation mechanisms, to finally provide a minimal agent-friendly shell.

As an example, Isar involves tens of various commands (e.g., `have, moreover, ultimately, obtain, hence, thus, show, shows, assume, assumes, lemma, theorem, corollary, by, apply, done, qed, proof, ., ..`) and sub-systems (attribute system, tactic system, documentation system, module system), Isabelle also provides tens of tactics (`this, rule, erule, drule, subst, simp, auto, linarith, blast, fast, fastforce, force, smt, metis, meson`). The differences between the commands and the tactics can be tiny or subtle. Many sub-systems are irrelevant to naked theorem proving. We believe, most of the stuffs can be eliminated for machine learning. Our shell only involves less-than-10 commands (see ??? for details).

This project still remains at the proposal stage. Any suggestions, feature requests, and concerns are welcome. Please contribute by opening a Github issue.

Please visit [doc](./doc) for the current proposal.

#!/usr/bin/env python3
"""Guard for the ONE piece of English prose that couples `library/proof.ML` to
`model.py`'s `Define`.

This is a PURE unit test (no Isabelle / no REPL): run it directly with
`python test_default_termination_error_coupling.py`; it exits non-zero on any
failure.

WHAT IT GUARDS. When Isabelle's default termination prover fails and the agent
supplied no metric, the ML side raises an error whose wording addresses someone
hand-writing a `.thy` file: it tells them to add a `BY_METRIC` clause. The AoA
agent never writes Minilang surface syntax -- it fills a `metric` tool field --
so `Define._beginning_opr_err_msgs` RECOGNISES that error and substitutes a
tool-level instruction. The recognition is a substring match against the ML
prose (`Define._DEFAULT_TERMINATION_FAILED`).

That coupling has no compiler and no type to protect it. Reword the ML message
-- "default" -> "automatic", say -- and nothing breaks loudly: the match simply
stops firing and the agent silently starts receiving advice it cannot act on.
The only other guard is a pair of "keep these in sync" comments. This test is
what makes the drift fail immediately instead of silently.

WHY IT READS THE FILES INSTEAD OF IMPORTING THEM. `model.py` pulls in the whole
agent stack; this test must stay runnable with no dependencies, in a plain
checkout, in CI, and while the REPL is down. So it reads the constant out of
`model.py` by regex rather than importing it -- which also means renaming the
constant fails here loudly, on purpose.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODEL_PY = HERE / "model.py"
PROOF_ML = HERE.parent.parent / "library" / "proof.ML"

# The opening of the DefaultFailed message in proof.ML. Both emission sites
# (run_phase_2's, and the eager DEFINE-time one added for the merged deferred
# block) raise this same text.
DEFAULT_FAILED_OPENING = "FUN: the default termination prover failed to prove "


def read_constant() -> str:
    """`Define._DEFAULT_TERMINATION_FAILED`, read out of model.py's source."""
    src = MODEL_PY.read_text(encoding="utf-8")
    m = re.search(r'^\s*_DEFAULT_TERMINATION_FAILED\s*=\s*"([^"]*)"\s*$',
                  src, re.MULTILINE)
    if m is None:
        sys.exit(
            f"FAIL: no `_DEFAULT_TERMINATION_FAILED = \"...\"` assignment in "
            f"{MODEL_PY}.\n"
            "If the constant was renamed or inlined, update this test to match; "
            "if the substitution in `Define._beginning_opr_err_msgs` was removed "
            "altogether, delete this test.")
    return m.group(1)


def error_sites(needle: str) -> list[tuple[int, str]]:
    """Lines of proof.ML that both raise an error and contain `needle`.

    The message opens on the same physical line as `error (` at every current
    site, so a line-wise test is enough and keeps this readable. A comment
    mentioning the phrase (there is one at each site, pointing here) does not
    contain `error (`, so it is correctly ignored.
    """
    out = []
    for i, line in enumerate(PROOF_ML.read_text(encoding="utf-8").splitlines(), 1):
        if "error (" in line and needle in line:
            out.append((i, line.strip()))
    return out


def main() -> None:
    for p in (MODEL_PY, PROOF_ML):
        if not p.is_file():
            sys.exit(f"FAIL: expected file not found: {p}")

    needle = read_constant()
    if not needle.strip():
        sys.exit("FAIL: `_DEFAULT_TERMINATION_FAILED` is empty or blank; it would "
                 "match every error message.")

    sites = error_sites(needle)
    default_failed = [s for s in sites if DEFAULT_FAILED_OPENING in s[1]]
    others = [s for s in sites if DEFAULT_FAILED_OPENING not in s[1]]

    # 1. The substitution must still fire. Both DefaultFailed sites must match.
    if len(default_failed) < 2:
        sys.exit(
            "FAIL: expected at least 2 `error (` sites in\n"
            f"  {PROOF_ML}\n"
            f"whose message opens with {DEFAULT_FAILED_OPENING!r} and contains the "
            f"substring {needle!r},\n"
            f"but found {len(default_failed)}.\n\n"
            "The two sites are run_phase_2's DefaultFailed branch and the eager "
            "DEFINE-time one.\nIf the ML wording changed, update "
            "`Define._DEFAULT_TERMINATION_FAILED` in model.py to match -- "
            "otherwise\nthe agent will start receiving the hand-written-.thy "
            "advice (\"provide a BY_METRIC clause\"),\nwhich it has no way to act "
            "on.")

    # 2. Anything ELSE matching the substring is a message the substitution
    #    would ALSO rewrite. Today there is exactly one: the "metric supplied
    #    but it did not close the obligations, and open_on_fail is false" error.
    #    It is unreachable from AoA -- agent.ML's DEFINE always passes
    #    open_on_fail = true -- so the over-match is harmless. If that count
    #    moves, the new site's reachability has to be re-checked by hand.
    if len(others) != 1:
        sys.exit(
            f"FAIL: expected exactly 1 non-DefaultFailed `error (` site matching "
            f"{needle!r},\nfound {len(others)}:\n"
            + "".join(f"  proof.ML:{n}: {t}\n" for n, t in others)
            + "\nEvery site listed here is a message that "
            "`Define._beginning_opr_err_msgs` would replace with\n"
            "\"...no metric was given...\". For a site where a metric WAS given "
            "that text is a lie.\nCheck whether the new site can reach a Define "
            "(agent.ML's DEFINE passes open_on_fail = true),\nand either narrow "
            "the substring or update this expectation.")

    print(f"OK  substring {needle!r}")
    for n, _ in default_failed:
        print(f"OK  DefaultFailed site      proof.ML:{n}")
    for n, _ in others:
        print(f"OK  known benign over-match proof.ML:{n} (unreachable from Define)")


if __name__ == "__main__":
    main()

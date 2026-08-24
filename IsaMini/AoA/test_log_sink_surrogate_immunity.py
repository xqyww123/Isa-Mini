#!/usr/bin/env python3
"""Standalone unit test: the diagnostic log sinks survive lone UTF-16
surrogates.

Background: a Claude Code CLI streaming bug can corrupt tool-call input so a
non-BMP character loses half its surrogate pair; ``json.loads`` happily hands
Python a ``str`` containing the lone surrogate (e.g. ``"\\ud835"``). The sink
that really crashed on it was ``_log_meta`` (strict ``str.encode``) — fixed
with ``ensure_ascii=False`` + ``errors="backslashreplace"``, which keeps
normal Unicode greppable and writes a lone surrogate as its lossless
``\\udXXX`` literal. The five YAML handles never crashed: their only writer is
``yaml.dump``, and PyYAML itself escapes surrogate-range code points
losslessly (verified below by reload equality); their
``errors="backslashreplace"`` is defence in depth only. proof.yaml
(``refresh_YAML``) deliberately stays strict; the proof tree is protected at
the tool-dispatch entry instead.

No Isabelle / no REPL. Run directly:  ``python test_log_sink_surrogate_immunity.py``.
Exits non-zero on any failure.
"""
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.model import Session, Role_Major

# The incident's exact shape: lone high surrogate (first half of 𝗏, U+1D5CF)
# followed by an unrelated BMP char the CLI synthesised.
CORRUPT = "\ud835≿0 corrupted"

failures = []


def check(cond, msg):
    if not cond:
        failures.append(msg)
        print(f"FAIL: {msg}")
    else:
        print(f"ok:   {msg}")


def make_session(log_dir):
    """A bare Session with only what _setup_log_directory/_log_meta need."""
    s = Session.__new__(Session)
    s.logger = None
    s.role = Role_Major()
    s._setup_log_directory(log_dir)
    return s


def main():
    with tempfile.TemporaryDirectory() as tmp:
        s = make_session(os.path.join(tmp, "logs"))

        handles = [s.interaction_log_file, s.proofs_log_file,
                   s.proof_oprs_log_file, s.retrieval_log_file,
                   s.missing_lemmas_log_file]
        for h in handles:
            name = os.path.basename(h.name)
            try:
                s._append_yaml(h, {"event": "TEST", "text": CORRUPT})
                check(True, f"_append_yaml with lone surrogate -> {name}")
            except Exception as e:
                check(False, f"_append_yaml raised on {name}: {e!r}")

        # Attribution: PyYAML itself escapes the surrogate LOSSLESSLY — the
        # document reloads to the identical str, proving the handles' errors=
        # never fired (it would have written six literal ASCII chars instead).
        import yaml
        s.interaction_log_file.flush()
        with open(s.interaction_log_path, encoding="utf-8") as f:
            docs = [d for d in yaml.safe_load_all(f)
                    if isinstance(d, dict) and d.get("event") == "TEST"]
        check(bool(docs) and docs[-1]["text"] == CORRUPT,
              "YAML round-trip is lossless (PyYAML's own escaping, not errors=)")

        try:
            s._log_meta("TEST_EVENT", text=CORRUPT)
            check(True, "_log_meta with lone surrogate does not raise")
        except Exception as e:
            check(False, f"_log_meta raised: {e!r}")
        s._log_meta("TEST_EVENT2", text="unicode ≿ stays greppable")

        import json
        import zstandard
        s._meta_log_writer.close()
        s._meta_log_writer = None
        with open(s.meta_log_path, "rb") as f:
            raw = zstandard.ZstdDecompressor().stream_reader(f).read()
        # Expected bytes (property, not a diff against old code): the lone
        # surrogate lands as its \udXXX literal; normal Unicode as raw UTF-8.
        check(rb"\ud835" in raw, "meta writes the lone surrogate as \\udXXX")
        check("≿".encode("utf-8") in raw,
              "meta keeps normal Unicode greppable (raw UTF-8, not \\uXXXX)")
        lines = raw.decode("utf-8", errors="surrogatepass").splitlines()
        corrupt_line = json.loads(lines[-2])
        check(corrupt_line["text"] == CORRUPT, "meta round-trip is lossless")

        # proof.yaml stays STRICT — lock: refresh_YAML opens without errors=.
        import inspect
        from IsaMini.AoA.driver_claude_code import ClaudeCode
        check("errors=" not in inspect.getsource(ClaudeCode.refresh_YAML),
              "proof.yaml handle must stay strict (no errors= in refresh_YAML)")

        s._meta_log_file.close()
        for h in handles:
            h.close()

    if failures:
        print(f"\n{len(failures)} FAILURE(S)")
        sys.exit(1)
    print("\nall passed")


if __name__ == "__main__":
    main()

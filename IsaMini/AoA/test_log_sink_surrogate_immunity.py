#!/usr/bin/env python3
"""Standalone unit test: the diagnostic log sinks survive lone UTF-16
surrogates.

Background: a Claude Code CLI streaming bug can corrupt tool-call input so a
non-BMP character loses half its surrogate pair; ``json.loads`` happily hands
Python a ``str`` containing the lone surrogate (e.g. ``"\\ud835"``). Strict
UTF-8 log sinks then raise ``UnicodeEncodeError`` while *logging* the corrupted
model output — before any recovery branch can run — killing the whole ``by
aoa`` command. The fix: the five YAML log handles open with
``errors="backslashreplace"`` and ``_log_meta`` uses ``ensure_ascii=True``.
proof.yaml (``refresh_YAML``) deliberately stays strict; the proof tree is
protected at the tool-dispatch entry instead.

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

        try:
            s._log_meta("TEST_EVENT", text=CORRUPT)
            check(True, "_log_meta with lone surrogate does not raise")
        except Exception as e:
            check(False, f"_log_meta raised: {e!r}")

        # Round-trip: the meta line must be lossless (\udXXX escape survives
        # json.loads back into the identical str).
        import json
        import zstandard
        s._meta_log_writer.close()
        s._meta_log_writer = None
        with open(s.meta_log_path, "rb") as f:
            raw = zstandard.ZstdDecompressor().stream_reader(f).read()
        last = json.loads(raw.decode("utf-8", errors="surrogatepass")
                          .splitlines()[-1])
        check(last["text"] == CORRUPT, "meta round-trip is lossless")

        s._meta_log_file.close()
        for h in handles:
            h.close()

    if failures:
        print(f"\n{len(failures)} FAILURE(S)")
        sys.exit(1)
    print("\nall passed")


if __name__ == "__main__":
    main()

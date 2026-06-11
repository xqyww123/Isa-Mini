"""Unit test: `_validate_fact_by_name` rejects propositions pasted where a
fact NAME belongs (discharge entries, top-level fact names), while letting
every legal reference shape through untouched.

Pure Python — no Isabelle, no REPL, no LLM.

Usage:
  python -m IsaMini.AoA.test_fact_name_validation
"""

from IsaMini.AoA.model import (
    ArgumentError, FactByName, Obvious, validate, _fact_ref_is_proposition,
)


def _expect_reject(data, path: str, *needles: str) -> None:
    try:
        validate(FactByName, data, path)
    except ArgumentError as e:
        msg = str(e)
        for needle in needles:
            assert needle in msg, (
                f"expected {needle!r} in error for {data!r} at {path}, "
                f"got:\n{msg}")
        return
    raise AssertionError(f"{data!r} at {path} was accepted, expected reject")


def _expect_accept(data, path: str) -> None:
    out = validate(FactByName, data, path)
    assert isinstance(out, dict) and "name" in out, \
        f"unexpected canonical form for {data!r}: {out!r}"


def main() -> None:
    # --- the incident (putnam_1987_a2, eb6c5d71c_1): propositions in discharge
    _expect_reject("k \N{LESS-THAN OR EQUAL TO} k", "facts[0].discharge[0]",
                   "facts[0].discharge[0]", "is a proposition",
                   "pass null")
    _expect_reject("\N{FOR ALL}(y::nat). y \N{LESS-THAN OR EQUAL TO} k "
                   "\N{LONG RIGHTWARDS ARROW} y \N{LESS-THAN OR EQUAL TO} k",
                   "facts[0].discharge[1]",
                   "facts[0].discharge[1]", "is a proposition")
    # no whitespace, but a banned relational symbol at top level
    _expect_reject("k\N{LESS-THAN OR EQUAL TO}k", "facts[0].discharge[0]",
                   "is a proposition")
    # dict form: error location points at the `name` field
    _expect_reject({"name": "k \N{LESS-THAN OR EQUAL TO} k"}, "facts[0]",
                   "facts[0].name", '{"proposition": "..."}')
    # context without a FactByProposition alternative: no `proposition` hint
    try:
        validate(FactByName, {"name": "x = y"}, "rule")
    except ArgumentError as e:
        assert "proposition\": " not in str(e), str(e)
        assert "is a proposition" in str(e), str(e)
    else:
        raise AssertionError("rule with propositional name was accepted")
    # Derive's discharging_facts gets the discharge-flavoured message
    _expect_reject("x = y", "discharging_facts[0]", "discharge entry")

    # --- legal reference shapes must pass
    for ok in [
        "Greatest_equality",
        "foo.bar(2)[OF x]",                        # qualified + selector + attrs
        "assms(1)",
        "assms(1, 2)",                             # whitespace inside selector
        "assms(1-3)",
        "foo[where x = \N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}a b"
        "\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}]",  # ws in attr group
        "\N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}k "
        "\N{LESS-THAN OR EQUAL TO} k"
        "\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}",   # literal fact
        "\N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}k "
        "\N{LESS-THAN OR EQUAL TO} k"
        "\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}[symmetric]",
        "foo'",
        "local.divide_le_eq",
    ]:
        _expect_accept(ok, "facts[0].discharge[0]")
    # not clearly propositional -> leave to the ML parser (high precision)
    for borderline in ["", "foo[OF", "foo]bar", "foo)("]:
        assert not _fact_ref_is_proposition(borderline), borderline
        _expect_accept(borderline, "facts[0].discharge[0]") \
            if borderline else None
    # int name fields are coerced to str by the scalar validator, then checked
    _expect_accept({"name": 123}, "facts[0].discharge[0]")

    # --- replay the incident's full edit arg through the real gen path
    try:
        Obvious.gen_single({"facts": [{
            "name": "Greatest_equality",
            "instantiations": [
                {"name": "?P", "value": "\N{GREEK SMALL LETTER LAMDA}(k1::nat)."
                                        " k1 \N{LESS-THAN OR EQUAL TO} k"},
                {"name": "?x", "value": "k"}],
            "discharge": [
                "k \N{LESS-THAN OR EQUAL TO} k",
                "\N{FOR ALL}(y::nat). y \N{LESS-THAN OR EQUAL TO} k "
                "\N{LONG RIGHTWARDS ARROW} y \N{LESS-THAN OR EQUAL TO} k"],
            "flip": False}]})
    except ArgumentError as e:
        msg = str(e)
        assert "discharge[0]" in msg and "is a proposition" in msg, msg
        print("incident replay error message:\n" + msg + "\n")
    else:
        raise AssertionError("incident arg was accepted, expected reject")

    print("all fact-name validation tests passed")


if __name__ == "__main__":
    main()

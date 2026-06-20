"""Unit test: `_collect_query_warnings` renders query-tool warnings through
`pretty_unicode`, so a parse-error marker whose snippet contains an Isabelle
ascii symbol (e.g. \\<oplus>) reaches the agent as unicode (⊕) — matching the
unicode entity names shown elsewhere in query output — while the raw-UTF-8
marker bytes 【 】 ↳ … — pass through untouched.

This covers the live `query` tool path (mcp_http_server → _query_tool_logic →
_semantic_search_* → _collect_query_warnings), which the SemanticKNN model
tests bypass (they call ml.semantic_knn directly and format warnings by hand).

Pure Python — no Isabelle, no REPL, no LLM.

Usage:
  python -m IsaMini.AoA.test_query_warning_unicode
"""

from IsaMini.AoA.retrieval import _collect_query_warnings, _KnnQueryResult

OPLUS = "⊕"        # ⊕  = \<oplus>
LBRACK = "【"       # 【
RBRACK = "】"       # 】
ARROW = "↳"        # ↳
EMDASH = "—"       # —


def main() -> None:
    # A realistic term-pattern parse-error warning as the ML side returns it:
    # the marker splices the ORIGINAL pattern string, which over RPC is ascii
    # \<name> form; the 【】/↳/— glyphs are already raw UTF-8.
    marker_warning = (
        f"Term pattern was ignored {EMDASH} results are NOT filtered by it.\n"
        f"Inner syntax error\nFailed to parse term\n"
        f"  {ARROW} x \\<oplus> {LBRACK}parsing fails here{RBRACK}bad"
    )
    # _KnnQueryResult = (fetched, warnings, error, total)
    knn_results: list[_KnnQueryResult] = [([], [marker_warning], None, 0)]
    per_query = _collect_query_warnings(knn_results)
    out = per_query[0][0]

    assert out.startswith("Warning: "), f"missing 'Warning: ' prefix: {out!r}"
    # the ascii symbol was converted to unicode ...
    assert OPLUS in out, f"\\<oplus> not rendered to ⊕: {out!r}"
    assert "\\<oplus>" not in out, f"raw \\<oplus> leaked to agent: {out!r}"
    # ... while the marker/structure bytes survive untouched
    for ch in (LBRACK, RBRACK, ARROW, EMDASH):
        assert ch in out, f"marker byte {ch!r} mangled: {out!r}"

    # the `error` field is rendered the same way
    err_results: list[_KnnQueryResult] = [([], [], "Undefined type name: \\<oplus>foo", 7)]
    err_out = _collect_query_warnings(err_results)[0][0]
    assert OPLUS in err_out and "\\<oplus>" not in err_out, \
        f"error field not unicode-rendered: {err_out!r}"

    # symbol-free warnings pass through byte-identical
    plain = "No loaded theory name contains \"Nonexistent_Theory_XYZ\" in theories_include; skipped"
    plain_results: list[_KnnQueryResult] = [([], [plain], None, 0)]
    plain_out = _collect_query_warnings(plain_results)[0][0]
    assert plain_out == f"Warning: {plain}", f"plain warning altered: {plain_out!r}"

    print("OK: _collect_query_warnings renders \\<name> -> unicode, preserves 【】↳…—, leaves plain text intact")


if __name__ == "__main__":
    main()

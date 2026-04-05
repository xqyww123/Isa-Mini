#!/usr/bin/env python3
"""Show retrieval training DB contents."""

import argparse
import json
import sqlite3
import sys

import platformdirs


def main():
    parser = argparse.ArgumentParser(
        description="Show retrieval training DB contents.")
    parser.add_argument("n", nargs="?", type=int, default=None,
                        help="Number of records to show (default: count only)")
    parser.add_argument("--db", default=None,
                        help="Path to DB file (default: standard cache location)")
    args = parser.parse_args()

    if args.db:
        db_path = args.db
    else:
        cache_dir = platformdirs.user_cache_dir("Isabelle_Semantic_Embedding", "Qiyuan")
        db_path = f"{cache_dir}/AoA_Collected/retrieval_training.db"

    try:
        conn = sqlite3.connect(db_path)
    except sqlite3.Error as e:
        print(f"Cannot open DB at {db_path}: {e}", file=sys.stderr)
        sys.exit(1)

    try:
        (total,) = conn.execute("SELECT COUNT(*) FROM retrieval_events").fetchone()
    except sqlite3.OperationalError:
        print(f"Table 'retrieval_events' not found in {db_path}", file=sys.stderr)
        sys.exit(1)

    print(f"Total records: {total}  ({db_path})")

    if args.n is not None:
        rows = conn.execute(
            "SELECT id, timestamp, query, kinds, interaction_type, "
            "candidates, selected_indices, prove_in_time "
            "FROM retrieval_events ORDER BY id LIMIT ?", (args.n,)
        ).fetchall()

        for row in rows:
            id_, ts, query, kinds, itype, cands_json, sel_json, pit = row
            cands = json.loads(cands_json)
            selected = json.loads(sel_json)
            print(f"\n{'='*60}")
            print(f"#{id_} [{ts}] {itype}")
            print(f"  query: {query}")
            print(f"  kinds: {kinds}")
            print(f"  candidates ({len(cands)}):")
            for c in cands:
                marker = " ✓" if c["selected"] else ""
                expr = c.get("expression", [])
                expr_str = f": {', '.join(expr)}" if expr else ""
                print(f"    [{c['score']:.2f}] {c['full_name']}{expr_str}{marker}")
            print(f"  selected: {selected}")
            if pit:
                print(f"  prove-in-time: {pit}")

    conn.close()


if __name__ == "__main__":
    main()

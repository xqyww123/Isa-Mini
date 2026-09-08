"""The L1 proof store: a SQLite wrapper, NOT part of the AoA agent stack.

L1 mirrors the ML-side L2 (Phi_Proof_Store): same key (the all-goals hash of
the goal before any preprocessing, no epoch prefix) and same value shape —
(standard-machine times, proof text), the times being the thread CPU ms and
the wall ms of the proof's replay.  Rows move between the levels verbatim.
The proof text is an Isar method text (e.g. 'aoa_replay "<b64>"' or
'metis …'); this module never decodes a blob — the blob format is known only
to the ML-side assembler (raw_AoA) and decoder (the aoa_replay method).

Three RPCs (IsaMini.ProofStore.lookup / store / invalidate) serve the ML side;
loading this module must never pull in the agent stack, so a lookup on a
machine that never runs an agent stays one process start + one SQLite query.
On the wire the times are (cpu_ms, wall_ms) nested in one slot, as at every
wire carrying a Phi_Proof_Store.times.
"""

import sqlite3
import os
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from platformdirs import user_cache_dir

_V2_COLUMNS = {"goal_hash", "proof_text", "std_cpu_ms", "std_wall_ms", "timestamp"}
_LEGACY_COLUMNS = {"goal_hash", "proof_text", "std_time_ms", "timestamp"}


class ProofStore:
    """SQLite-backed level 1: goal_hash -> ((std_cpu_ms, std_wall_ms), proof_text)."""

    def __init__(self, db_path: str | os.PathLike | None = None):
        if db_path is None:
            cache_dir = user_cache_dir("IsaMini")
            os.makedirs(cache_dir, exist_ok=True)
            db_path = os.path.join(cache_dir, "aoa_proof_cache.db")
        self.db_path = str(db_path)
        self._conn = sqlite3.connect(self.db_path)
        self._conn.execute("PRAGMA journal_mode=WAL")
        # Auto cold start (round-4 review): a table of any shape but the
        # expected one is dropped; L1 is a cache, losing it costs one re-search
        # per goal.  The single-time table `proof_cache` is never created here
        # and, in its legacy shape, never modified: it is read once, below.
        if self._columns("proof_cache_v2") not in (set(), _V2_COLUMNS):
            self._conn.execute("DROP TABLE proof_cache_v2")
        self._conn.execute("""
            CREATE TABLE IF NOT EXISTS proof_cache_v2 (
                goal_hash   TEXT    PRIMARY KEY,
                proof_text  TEXT    NOT NULL,
                std_cpu_ms  INTEGER NOT NULL,
                std_wall_ms INTEGER NOT NULL,
                timestamp   REAL    NOT NULL
            )
        """)
        if self._columns("proof_cache") not in (set(), _LEGACY_COLUMNS):
            # the agent-era table of the same name, with a proof_json column
            self._conn.execute("DROP TABLE proof_cache")
        # Migration: a single-time row's ms fills both times.  Gated on the new
        # table being empty rather than newly created, so an open interrupted
        # after the CREATE (sqlite3 does not wrap DDL in a transaction) is
        # repaired by the next one.
        if self._columns("proof_cache") == _LEGACY_COLUMNS \
                and self._conn.execute("SELECT 1 FROM proof_cache_v2 LIMIT 1").fetchone() is None:
            self._conn.execute("""
                INSERT OR IGNORE INTO proof_cache_v2
                SELECT goal_hash, proof_text, std_time_ms, std_time_ms, timestamp FROM proof_cache
            """)
        self._conn.commit()

    def _columns(self, table: str) -> set[str]:
        return {row[1] for row in self._conn.execute(f"PRAGMA table_info({table})")}

    def lookup(self, goal_hash: str) -> tuple[tuple[int, int], str] | None:
        row = self._conn.execute(
            "SELECT std_cpu_ms, std_wall_ms, proof_text FROM proof_cache_v2 WHERE goal_hash = ?",
            (goal_hash,)
        ).fetchone()
        if row is None:
            return None
        return ((row[0], row[1]), row[2])

    def store(self, goal_hash: str, std_times_ms: tuple[int, int], proof_text: str) -> None:
        from time import time
        std_cpu_ms, std_wall_ms = std_times_ms
        self._conn.execute(
            "INSERT OR REPLACE INTO proof_cache_v2"
            " (goal_hash, proof_text, std_cpu_ms, std_wall_ms, timestamp)"
            " VALUES (?, ?, ?, ?, ?)",
            (goal_hash, proof_text, std_cpu_ms, std_wall_ms, time())
        )
        self._conn.commit()

    def invalidate(self, goal_hash: str) -> None:
        """Delete one row — the L1 mirror of the L2 tombstone, sent by the ML
        side after a hit whose replay failed."""
        self._conn.execute(
            "DELETE FROM proof_cache_v2 WHERE goal_hash = ?", (goal_hash,))
        self._conn.commit()

    def close(self) -> None:
        self._conn.close()


_store: ProofStore | None = None


def get_proof_store() -> ProofStore:
    global _store
    if _store is None:
        _store = ProofStore()
    return _store


@isabelle_remote_procedure("IsaMini.ProofStore.lookup")
async def _lookup_rpc(goal_hash: str, connection: Connection) -> tuple[tuple[int, int], str] | None:
    return get_proof_store().lookup(goal_hash)


@isabelle_remote_procedure("IsaMini.ProofStore.store")
async def _store_rpc(arg: tuple[str, tuple[int, int], str], connection: Connection) -> None:
    goal_hash, std_times_ms, proof_text = arg
    get_proof_store().store(goal_hash, std_times_ms, proof_text)


@isabelle_remote_procedure("IsaMini.ProofStore.invalidate")
async def _invalidate_rpc(goal_hash: str, connection: Connection) -> None:
    get_proof_store().invalidate(goal_hash)

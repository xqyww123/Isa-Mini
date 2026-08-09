"""The L1 proof store: a SQLite wrapper, NOT part of the AoA agent stack.

L1 mirrors the ML-side L2 (Phi_Proof_Store): same key (the all-goals hash of
the goal before any preprocessing, no epoch prefix) and same value shape —
(standard-machine time, proof text).  Rows move between the levels verbatim.
The proof text is an Isar method text (e.g. 'aoa_replay "<b64>"' or
'metis …'); this module never decodes a blob — the blob format is known only
to the ML-side assembler (raw_AoA) and decoder (the aoa_replay method).

Three RPCs (IsaMini.ProofStore.lookup / store / invalidate) serve the ML side;
loading this module must never pull in the agent stack, so a lookup on a
machine that never runs an agent stays one process start + one SQLite query.
"""

import sqlite3
import os
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from platformdirs import user_cache_dir


class ProofStore:
    """SQLite-backed level 1: goal_hash -> (std_time_ms, proof_text)."""

    def __init__(self, db_path: str | os.PathLike | None = None):
        if db_path is None:
            cache_dir = user_cache_dir("IsaMini")
            os.makedirs(cache_dir, exist_ok=True)
            db_path = os.path.join(cache_dir, "aoa_proof_cache.db")
        self.db_path = str(db_path)
        self._conn = sqlite3.connect(self.db_path)
        self._conn.execute("PRAGMA journal_mode=WAL")
        # Table and file names are historical (the one-off cold start wiped the
        # old contents); the schema is the new proof-text one.
        self._conn.execute("""
            CREATE TABLE IF NOT EXISTS proof_cache (
                goal_hash   TEXT    PRIMARY KEY,
                proof_text  TEXT    NOT NULL,
                std_time_ms INTEGER NOT NULL,
                timestamp   REAL    NOT NULL
            )
        """)
        self._conn.commit()

    def lookup(self, goal_hash: str) -> tuple[int, str] | None:
        row = self._conn.execute(
            "SELECT std_time_ms, proof_text FROM proof_cache WHERE goal_hash = ?",
            (goal_hash,)
        ).fetchone()
        if row is None:
            return None
        return (row[0], row[1])

    def store(self, goal_hash: str, std_time_ms: int, proof_text: str) -> None:
        from time import time
        self._conn.execute(
            "INSERT OR REPLACE INTO proof_cache (goal_hash, proof_text, std_time_ms, timestamp)"
            " VALUES (?, ?, ?, ?)",
            (goal_hash, proof_text, std_time_ms, time())
        )
        self._conn.commit()

    def invalidate(self, goal_hash: str) -> None:
        """Delete one row — the L1 mirror of the L2 tombstone, sent by the ML
        side after a hit whose replay failed."""
        self._conn.execute(
            "DELETE FROM proof_cache WHERE goal_hash = ?", (goal_hash,))
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
async def _lookup_rpc(goal_hash: str, connection: Connection) -> tuple[int, str] | None:
    return get_proof_store().lookup(goal_hash)


@isabelle_remote_procedure("IsaMini.ProofStore.store")
async def _store_rpc(arg: tuple[str, int, str], connection: Connection) -> None:
    goal_hash, std_time_ms, proof_text = arg
    get_proof_store().store(goal_hash, std_time_ms, proof_text)


@isabelle_remote_procedure("IsaMini.ProofStore.invalidate")
async def _invalidate_rpc(goal_hash: str, connection: Connection) -> None:
    get_proof_store().invalidate(goal_hash)

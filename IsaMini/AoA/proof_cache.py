import sqlite3
import json
import os
from typing import Any
from platformdirs import user_cache_dir


class ProofCache:
    """SQLite-backed cache: goal_hash -> serialized xcmd list (JSON)."""

    def __init__(self, db_path: str | os.PathLike | None = None):
        if db_path is None:
            cache_dir = user_cache_dir("IsaMini")
            os.makedirs(cache_dir, exist_ok=True)
            db_path = os.path.join(cache_dir, "aoa_proof_cache.db")
        self.db_path = str(db_path)
        self._conn = sqlite3.connect(self.db_path)
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._conn.execute("""
            CREATE TABLE IF NOT EXISTS proof_cache (
                goal_hash TEXT PRIMARY KEY,
                proof_json TEXT NOT NULL,
                timestamp REAL NOT NULL
            )
        """)
        self._conn.commit()

    def lookup(self, goal_hash: str) -> list[Any] | None:
        row = self._conn.execute(
            "SELECT proof_json FROM proof_cache WHERE goal_hash = ?",
            (goal_hash,)
        ).fetchone()
        if row is None:
            return None
        return json.loads(row[0])

    def store(self, goal_hash: str, packed_ops: list[Any]) -> None:
        from time import time
        self._conn.execute(
            "INSERT OR REPLACE INTO proof_cache (goal_hash, proof_json, timestamp) VALUES (?, ?, ?)",
            (goal_hash, json.dumps(packed_ops), time())
        )
        self._conn.commit()

    def close(self) -> None:
        self._conn.close()


_cache: ProofCache | None = None


def get_proof_cache() -> ProofCache:
    global _cache
    if _cache is None:
        _cache = ProofCache()
    return _cache

-- AoA usage count: one row per (UTC day, AoA version, platform).
--
-- Row count grows as (days) x (versions in use) x (platforms), i.e. tens of rows
-- per day at the very most.  `version` and `platform` are normalised by the
-- Worker to a small closed set of values before they ever reach here, so a
-- hostile client cannot mint unbounded rows.

CREATE TABLE IF NOT EXISTS daily (
  day          TEXT    NOT NULL,   -- server-side UTC date, 'YYYY-MM-DD'
  version      TEXT    NOT NULL,   -- AoA version, e.g. '0.6.0'; 'other' if unrecognised
  platform     TEXT    NOT NULL,   -- 'linux' | 'darwin' | 'win32' | 'other'

  -- EVERY execution of `by aoa`, whichever way it was served: replayed from the
  -- proof cache, or actually run by the agent.  This is the total.
  run_or_cache INTEGER NOT NULL DEFAULT 0,

  -- The subset of the above that got past the cache and entered the agent.
  -- Therefore real_run <= run_or_cache always, and (run_or_cache - real_run) is
  -- the number of executions that were served from the proof cache.
  --
  -- NOTE: "entered the agent" is not the same as "spent model tokens" -- a user
  -- who has not logged in to their model provider still produces real_run events
  -- that spend nothing.
  real_run     INTEGER NOT NULL DEFAULT 0,

  PRIMARY KEY (day, version, platform)
);

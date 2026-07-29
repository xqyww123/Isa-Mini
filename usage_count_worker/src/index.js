// AoA usage count endpoint.
//
// Counts how often `by aoa` is used.  One POST per execution, no identifier of
// any kind, no authentication.  The whole contract with the client is: accept the
// report, bump one day's row, answer 204.  The client never reads the response
// and swallows every failure, so nothing here can affect a user's proof.
//
// See ../../../AOA_USAGE_COUNT_PLAN.md for the design and the decisions behind it.

// Server-side UTC date.  Client clocks are never trusted: a skewed or wrongly
// zoned machine would otherwise file its events under the wrong day.
const DAY = () => new Date().toISOString().slice(0, 10);

// Which columns each event increments.
//
//   cache -- `by aoa` was served by replaying the proof cache; the agent never ran.
//   agent -- `by aoa` got past the cache and entered the agent.  Bumps BOTH columns,
//            because every real_run is also one execution of the method.
//
// Read it with Object.hasOwn, NEVER as a bare `EVENTS[x]` truthiness test: a plain
// object literal inherits Object.prototype, so {"event":"constructor"} would pass
// such a test and reach the SQL below.
const EVENTS = {
  cache: ["run_or_cache"],
  agent: ["run_or_cache", "real_run"],
};

// These bound the CARDINALITY of (version, platform), not merely their length.
// Every distinct (day, version, platform) tuple is a new primary-key row, so a
// filter that merely limits length would let one client mint unbounded rows,
// exhaust the daily row-write quota, and permanently poison the version query.
// Anything unrecognised is folded into the single literal 'other'.
const VERSION = /^[0-9]+(\.[0-9]+){0,3}([.-]?(a|b|rc|dev|post)[0-9]*)?$/;
const PLATFORMS = new Set(["linux", "darwin", "win32"]);

export default {
  async fetch(request, env) {
    if (request.method !== "POST") return new Response(null, { status: 405 });

    let body;
    try {
      body = await request.json();
    } catch {
      return new Response(null, { status: 400 });
    }
    if (!body || !Object.hasOwn(EVENTS, body.event)) {
      return new Response(null, { status: 400 });
    }

    const version = VERSION.test(body.version) ? body.version : "other";
    const platform = PLATFORMS.has(body.platform) ? body.platform : "other";

    // `cols` comes from the EVENTS allow-list above, never from the request, so
    // interpolating it into the statement carries no injection surface.  The
    // values, which DO come from the request, go through bound parameters.
    const cols = EVENTS[body.event];
    const sets = cols.map((c) => `${c} = ${c} + 1`).join(", ");

    try {
      await env.DB.prepare(
        `INSERT INTO daily (day, version, platform, run_or_cache, real_run)
         VALUES (?1, ?2, ?3, ?4, ?5)
         ON CONFLICT(day, version, platform) DO UPDATE SET ${sets}`
      )
        .bind(DAY(), version, platform, 1, cols.length === 2 ? 1 : 0)
        .run();
    } catch (e) {
      // D1 has documented transient failures: connection lost, storage object
      // reset, database reset after a code update, overload.  Do NOT retry --
      // this upsert is not idempotent, so retrying after a lost connection would
      // double-count.  Log it and drop the count; a lost count is a lost count.
      console.error("d1 upsert failed:", e);
    }

    return new Response(null, { status: 204 });
  },
};

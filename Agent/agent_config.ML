(*  Title:      Agent/agent_config.ML

The configuration of one run of the agent: the parts of MiniLang_Agent.config.
They live here, ahead of agent_plugin.ML and agent.ML in the load order,
because the registry of user operations names config in a user operation's
`run` and in its `env` (docs/USER_OPERATIONS.md, section 1); agent.ML
re-exports them unchanged.
*)

signature MINILANG_AGENT_CONFIG = sig

type budget = {
      timeout_seconds: int,
      max_tool_calls: int,
      max_retries: int
  }

type cfg = {
      auto_interpret_for_embedding: bool option
  }

datatype exec_mode = LIVE | REPLAY

type counters = {
    prem_counter: int Synchronized.var
  }
type config = cfg * budget * counters * exec_mode

end

structure MiniLang_Agent_Config : MINILANG_AGENT_CONFIG = struct

type budget = {
      timeout_seconds: int,
      max_tool_calls: int,
      max_retries: int
  }

type cfg = {
      auto_interpret_for_embedding: bool option
  }

datatype exec_mode = LIVE | REPLAY

type counters = {
    prem_counter: int Synchronized.var
  }
type config = cfg * budget * counters * exec_mode

end

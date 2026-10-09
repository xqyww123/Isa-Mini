(*  Title:      Agent/agent_plugin.ML

The registries of user operations and tasks (docs/USER_OPERATIONS.md,
sections 1 and 5.1).  A plugin theory registers here; the interpreter, the
codec and the start of a call read here.  Both registries ride on the
theory, so a `by aoa` sees exactly the plugins whose theories it imports,
and re-evaluating a registering theory registers once.
*)

signature MINILANG_AGENT_PLUGIN = sig
  type state_id = string
  type env = {
    state_of : state_id -> Minilang.state option,   (* raw_AoA's state table, by name *)
    config   : unit -> MiniLang_Agent_Config.config } (* the config of the moment it is read *)

  (* what a plugin writes, at its own argument type *)
  type 'a user_operation = {
    name         : string,                           (* the agent-facing operation name *)
    default      : bool,                             (* active in every call unless excluded *)
    unpack_arg   : 'a MessagePackBinIO.Unpack.unpacker,
    pack_arg     : 'a MessagePackBinIO.Pack.packer,
    run          : MiniLang_Agent_Config.config -> 'a -> Minilang.operation,
    pack_message : exn -> MessagePackBinIO.Pack.raw_packer option,
    callbacks    : env -> Remote_Procedure_Calling.callback' list }

  (* what the registry holds: the plugin's record over Universal.universal, and its packages *)
  type registration = {
    operation       : Universal.universal user_operation,
    python_packages : string list }

  type task = {name : string, payload : MessagePackBinIO.Pack.raw_packer}
  type user_operation_selection = (string * bool) list   (* (name, include?) *)

  val register_user_operation :
        {python_packages : string list} -> 'a user_operation -> theory -> theory
  val register_task :
        {python_packages : string list} -> {name : string} -> theory -> theory

  (* what the framework reads; a name no imported theory registers is an error *)
  val the_operation     : theory -> string -> registration
  val the_task          : theory -> string -> {python_packages : string list}
  val active_operations : theory -> user_operation_selection -> registration list  (* name order *)
end

structure MiniLang_Agent_Plugin : MINILANG_AGENT_PLUGIN = struct

type state_id = string
type env = {
  state_of : state_id -> Minilang.state option,
  config   : unit -> MiniLang_Agent_Config.config }

type 'a user_operation = {
  name         : string,
  default      : bool,
  unpack_arg   : 'a MessagePackBinIO.Unpack.unpacker,
  pack_arg     : 'a MessagePackBinIO.Pack.packer,
  run          : MiniLang_Agent_Config.config -> 'a -> Minilang.operation,
  pack_message : exn -> MessagePackBinIO.Pack.raw_packer option,
  callbacks    : env -> Remote_Procedure_Calling.callback' list }

type registration = {
  operation       : Universal.universal user_operation,
  python_packages : string list }

type task = {name : string, payload : MessagePackBinIO.Pack.raw_packer}
type user_operation_selection = (string * bool) list

(*Both registries follow one shape: a table by name whose entries carry a
  serial, so that the same registration reached through two import paths
  merges, while two registrations of one name do not.*)
val operation_kind = "User operation"
val task_kind = "User task"

fun registered_twice kind name = error (kind ^ " " ^ quote name ^ " is registered twice")
fun unregistered kind name = error (kind ^ " " ^ quote name ^ ": no imported theory registers it")

fun merge_tables kind tabs = Symtab.merge (eq_fst op =) tabs
  handle Symtab.DUP name => registered_twice kind name
fun insert kind name x tab = Symtab.update_new (name, (serial (), x)) tab
  handle Symtab.DUP _ => registered_twice kind name
fun lookup kind tab name =
  (case Symtab.lookup tab name of
     SOME (_, x) => x
   | NONE => unregistered kind name)

structure Operations = Theory_Data (
  type T = (serial * registration) Symtab.table
  val empty = Symtab.empty
  fun merge tabs = merge_tables operation_kind tabs
)

structure Tasks = Theory_Data (
  type T = (serial * {python_packages : string list}) Symtab.table
  val empty = Symtab.empty
  fun merge tabs = merge_tables task_kind tabs
)

(*The plugin's argument type is hidden under a tag of this registration's own,
  as Thread_Data.var hides its data: the stored unpack_arg injects, the stored
  pack_arg and run project.  No other tag is ever applied to these values.*)
fun register_user_operation {python_packages}
      ({name, default, unpack_arg, pack_arg, run, pack_message, callbacks} : 'a user_operation) =
  let val tag = Universal.tag ()
      val operation : Universal.universal user_operation =
        {name = name, default = default,
         unpack_arg = unpack_arg #> apfst (Universal.tagInject tag),
         pack_arg = pack_arg o Universal.tagProject tag,
         run = fn config => run config o Universal.tagProject tag,
         pack_message = pack_message, callbacks = callbacks}
   in Operations.map (insert operation_kind name {operation = operation, python_packages = python_packages})
  end

fun register_task {python_packages} {name} =
  Tasks.map (insert task_kind name {python_packages = python_packages})

fun the_operation thy name = lookup operation_kind (Operations.get thy) name
fun the_task thy name = lookup task_kind (Tasks.get thy) name

(*the registrations with default = true, plus the included, minus the excluded, in name order*)
fun active_operations thy selection =
  let val tab = Operations.get thy
      val _ = List.app (ignore o the_operation thy o fst) selection
      fun selected polarity name = member (op =) selection (name, polarity)
      fun active (name, (_, reg)) =
        (#default (#operation reg) orelse selected true name) andalso not (selected false name)
   in Symtab.dest tab |> filter active |> sort_by #1 |> map (#2 o #2) end

(*the two built-in tasks, registered as a plugin's are*)
val _ = Theory.setup
  (register_task {python_packages = []} {name = "usual"}
   #> register_task {python_packages = []} {name = "learning"})

end

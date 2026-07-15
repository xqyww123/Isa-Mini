# The Minilang REPL client (.REPL) wraps IsaREPL, an OPTIONAL dependency
# (`pip install IsaMini[repl]`). AoA never uses it and talks to Isabelle via
# Isabelle_RPC_Host instead, so IsaREPL's absence must NOT break `import IsaMini`
# (hence `import IsaMini.AoA`). When IsaREPL is present this binds `REPL` to the
# client class exactly as before; when it is absent, `import IsaMini` still
# succeeds and accessing `IsaMini.REPL` raises a clear, actionable ImportError.
#
# A module-level `__getattr__` alone cannot do this: `.REPL` is a real submodule
# with the same name, so `from IsaMini import REPL` binds the *module* rather
# than the class and never consults `__getattr__`. Hence the eager try/except.
try:
    from .REPL import REPL as REPL  # redundant alias: intentional re-export
except ImportError as _err:
    # Only IsaREPL-absence is the optional case; a different missing import
    # inside REPL.py is a real bug and must surface, not be masked by the hint.
    if (_err.name or "").split(".")[0] != "IsaREPL":
        raise
    # `except ... as _err` auto-deletes `_err` at block exit, so stash it under a
    # name that survives for the deferred __getattr__ below to chain from.
    _repl_import_error = _err

    def __getattr__(name):
        if name == "REPL":
            # Deliberately an ImportError (not AttributeError): the whole value of
            # accessing IsaMini.REPL without IsaREPL is this actionable install
            # hint. The trade-off is that `hasattr(IsaMini, "REPL")` propagates
            # rather than returning False -- acceptable, no in-repo caller probes it.
            raise ImportError(
                "IsaMini.REPL (the Minilang REPL client / `IsaMini` CLI) requires "
                "the optional IsaREPL dependency. Install it with "
                "`pip install IsaMini[repl]`. (The AoA agent does not need it.)"
            ) from _repl_import_error
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
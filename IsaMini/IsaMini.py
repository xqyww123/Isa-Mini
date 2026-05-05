import IsaREPL as REPL

class Mini:
    """
    A REPL client for Isabelle/Mini
    """

    VERSION='0.3.5'

    async def __run(self):
        await self.repl.run_app("Minilang-REPL")
        await self.repl._write((self.hasty, self.mode, self.SH_params))
        version = REPL.Client._parse_control_ (await self.repl._feed_and_unpack())
        if version != Mini.VERSION:
            raise Exception(f"Mini: incompatible client version {Mini.VERSION} of Server {version}")

    async def __turn_off (self):
        if self.pos:
            await self.repl._write("\\close")
            return REPL.Client._parse_control_ (await self.repl._feed_and_unpack())

    def __init__(self, addr, thy_qualifier, initial_pos = None, ML_base_injection=True, timeout=3600, hasty=False, SH_params=""):
        """
        Argument repl: a REPL client

        The REPL session will turn into Minilang mode, and return into the usual
        mode until this Mini instance is explicitly closed by the `close` method.
        A Mini intance can be created only when the REPL session is at a proof state.

        Before the REPL session turns into the usual mode, any method of the REPL
        client should not be called!

        :param initial_pos: Optional position (file,line,offset) from which the Mini
        instance will start.
        :param ML_base_injection: Internally used only. Please do not change its default value.
        """
        self._addr = addr
        self._thy_qualifier = thy_qualifier
        self._initial_pos = initial_pos
        self._ML_base_injection = ML_base_injection
        self._timeout = timeout
        self.pos = initial_pos
        self.mode = 'RELAXED'
        self.hasty = hasty
        self.SH_params = SH_params
        self.repl: REPL.Client = None  # type: ignore[assignment]  # set in __aenter__

    async def __aenter__(self):
        self.repl = REPL.Client(self._addr, self._thy_qualifier, self._timeout)
        await self.repl.__aenter__()
        await self.repl.set_trace(False)
        if not hasattr(self.repl, '_initialized_mini_'):
            await self.repl.load_theory (['Minilang_REPL.Minilang_Top'])
            if self._ML_base_injection:
                await self.repl.add_lib (["Minilang.Minilang_Base"])
            await self.repl.run_ML ("Minilang_REPL.Minilang_Top",
                """REPL_Server.register_app "Minilang-REPL" Minilang_Top.REPL_App""")
            self.repl._initialized_mini_ = True  # type: ignore[attr-defined]
        await self.repl.record_state ("mini-init")
        if self._initial_pos:
            await self.repl.file(self._initial_pos[0], self._initial_pos[1], self._initial_pos[2], use_cache=True, cache_position=True)
        if self.pos:
            await self.__run()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        await self.close()

    async def close(self):
        """
        Give up the ongoing proof, clos the Mini instance,
        and turns the REPL session into the usual mode.
        :return: None
        """
        await self.__turn_off()
        self.repl.close()

    async def conclude (self):
        """
        Closes the Mini instance, and turns the REPL session into the usual mode.
        :return:
        a pair of
            1. the pretty-print string of the proven thm
            2. the obtained proof.
        """
        if not self.pos:
            raise ValueError("Mini: not started yet. Call `move_to` to indicate where to start the proof.")
        await self.repl._write("\\conclude")
        return REPL.Client._parse_control_ (await self.repl._feed_and_unpack())

    async def set_mode(self, mode):
        if not isinstance(mode, str):
            raise TypeError("mode must be a string")
        if mode not in ['STRICT', 'COMPLETE_NEXT', 'RELAXED']:
            raise ValueError("mode must be one of: 'STRICT', 'COMPLETE_NEXT', 'RELAXED'")
        self.mode = mode
        if self.pos:
            await self.repl._write("\\END_mode", mode)
            REPL.Client._parse_control_ (await self.repl._feed_and_unpack())

    async def move_to (self, file, line, column=0):
        await self.__turn_off()
        await self.repl.rollback ('mini-init')
        await self.repl.file(file, line, column, use_cache=True, cache_position=True)
        self.pos = (file, line, column)
        await self.__run()

    async def set_theory_and_goal(self, src):
        await self.__turn_off()
        await self.repl.rollback('mini-init')
        await self.repl.eval(src)
        self.pos = ("#REPL", 0, 0)
        await self.__run()

    async def eval (self, src, timeout=None, timeout_cmd=None):
        """
        Evaluates the given source Minilang code.
        The given source can contain multiple commands.
        Returns the list of the respective proof states after evaluating each of the command.

        timeout: timeout in milliseconds
        timeout_cmd: timeout to wait for every single command, in milliseconds
        """
        if not self.pos:
            raise ValueError("Mini: not started yet. Call `move_to` to indicate where to start the proof.")
        if timeout is not None and not isinstance(timeout, int):
            raise TypeError("timeout must be an integer or None")
        if timeout_cmd is not None and not isinstance(timeout_cmd, int):
            raise TypeError("timeout_cmd must be an integer or None")
        if timeout is None and timeout_cmd is None:
            await self.repl._write(src)
        else:
            await self.repl._write("\\eval", (timeout, timeout_cmd, src))
        return REPL.Client._parse_control_ (await self.repl._feed_and_unpack())

    async def record(self, name):
        """
        record the current proof state with the given name, so that it can be retrieved later using `rollback` method.
        """
        await self.repl._write("\\stamp", name)
        return REPL.Client._parse_control_ (await self.repl._feed_and_unpack())

    async def rollback(self, name):
        """
        roll back to the proof state recorded with the given name.
        """
        await self.repl._write("\\rollback", name)
        return REPL.Client._parse_control_ (await self.repl._feed_and_unpack())


    @staticmethod
    def parse_item(data):
        return {
            'vars' : data[0],
            'facts': data[1]
        }

    @staticmethod
    def parse_prooftree (data):
        match data[0]:
            case 0:
                # a single proposition
                return {
                    'vars' : data[1][0],
                    'facts': data[1][1],
                    'goal' : data[2]
                }
            case 1:
                # a bundle
                return {
                    'vars' : data[1][0],
                    'facts': data[1][1],
                    'goal' : [Mini.parse_prooftree(x) for x in data[2]]
                }
            case 2:
                # a block
                return {
                    'block': Mini.parse_prooftree(data[1])
                }
    @staticmethod
    def parse_eval_return (response):
        data, status = response
        return {
            'new_items': Mini.parse_item (data[0]),
            'new_case' : data[1],
            'state'    : Mini.parse_prooftree (data[2]),
            'finished' : status
        }

    async def pretty_eval (self, src):
        ret = await self.eval (src)
        return Mini.parse_eval_return (ret)

    async def print(self):
        if not self.pos:
            raise ValueError("Mini: not started yet. Call `move_to` to indicate where to start the proof.")
        await self.repl._write('\\print')
        return REPL.Client._parse_control_(await self.repl._feed_and_unpack())

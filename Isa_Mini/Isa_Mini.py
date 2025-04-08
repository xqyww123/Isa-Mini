import msgpack as mp
import IsaREPL as REPL

class Mini:
    """
    A REPL client for Isabelle/Mini
    """

    VERSION='0.3.2'

    def __run(self):
        self.repl.run_app("Minilang-REPL")
        REPL.Client._parse_control_ (self.repl.unpack.unpack())
        mp.pack("\\END_mode", self.repl.cout)
        mp.pack(self.mode, self.repl.cout)
        self.repl.cout.flush()
        REPL.Client._parse_control_ (self.repl.unpack.unpack())

    def __turn_off (self):
        if self.pos:
            mp.pack ("\\close", self.repl.cout)
            self.repl.cout.flush()
            return REPL.Client._parse_control_ (self.repl.unpack.unpack())

    def __init__(self, addr, thy_qualifier, initial_pos = None, ML_base_injection=True, timeout=3600):
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

        self.repl = REPL.Client(addr, thy_qualifier, timeout)
        self.repl.set_trace(False)
        try:
            self.repl._initialized_mini_
        except AttributeError:
            self.repl.load_theory (['Minilang_REPL.Minilang_Top'])
            if ML_base_injection:
                self.repl.add_lib (["Minilang.Minilang_Base"])
            self.repl.run_ML ("Minilang_REPL.Minilang_Top",
                """REPL_Server.register_app "Minilang-REPL" Minilang_Top.REPL_App""")
            self.repl._initialized_mini_ = True
        self.repl.record_state ("mini-init")
        if initial_pos:
            self.repl.file(initial_pos[0], initial_pos[1], initial_pos[2], use_cache=True, cache_position=True)
        self.pos = initial_pos
        self.mode = 'RELAXED'
        if self.pos:
            self.__run()

    def close(self):
        """
        Give up the ongoing proof, clos the Mini instance,
        and turns the REPL session into the usual mode.
        :return: None
        """
        self.__turn_off()
        self.repl.close()

    def conclude (self):
        """
        Closes the Mini instance, and turns the REPL session into the usual mode.
        :return:
        a pair of
            1. the pretty-print string of the proven thm
            2. the obtained proof.
        """
        if not self.pos:
            raise ValueError("Mini: not started yet. Call `move_to` to indicate where to start the proof.")
        mp.pack ("\\conclude", self.repl.cout)
        self.repl.cout.flush()
        return REPL.Client._parse_control_ (self.repl.unpack.unpack())

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()

    def set_mode(self, mode):
        if not isinstance(mode, str):
            raise TypeError("mode must be a string")
        if mode not in ['STRICT', 'COMPLETE_NEXT', 'RELAXED']:
            raise ValueError("mode must be one of: 'STRICT', 'COMPLETE_NEXT', 'RELAXED'")
        self.mode = mode
        if self.pos:
            mp.pack("\\END_mode", self.repl.cout)
            mp.pack(mode, self.repl.cout)
            self.repl.cout.flush()
            REPL.Client._parse_control_ (self.repl.unpack.unpack())

    def move_to (self, file, line, column=0):
        self.__turn_off()
        self.repl.rollback ('mini-init')
        self.repl.file(file, line, column, use_cache=True, cache_position=True)
        self.pos = (file, line, column)
        self.__run()

    def set_theory_and_goal(self, src):
        self.__turn_off()
        self.repl.rollback('mini-init')
        self.repl.eval(src)
        self.pos = ("#REPL", 0, 0)
        self.__run()

    def eval (self, src, timeout=None):
        """
        Evaluates the given source Minilang code.
        The given source can contain multiple commands.
        Returns the list of the respective proof states after evaluating each of the command.
        """
        if not self.pos:
            raise ValueError("Mini: not started yet. Call `move_to` to indicate where to start the proof.")
        if timeout is not None and not isinstance(timeout, int):
            raise TypeError("timeout must be an integer or None")
        if timeout is None:
            mp.pack (src, self.repl.cout)
        else:
            mp.pack ("\\eval", self.repl.cout)
            mp.pack ((timeout, src), self.repl.cout)
        self.repl.cout.flush()
        return REPL.Client._parse_control_ (self.repl.unpack.unpack())

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

    def pretty_eval (self, src):
        ret = self.eval (src)
        return Mini.parse_eval_return (ret)

    def print(self):
        if not self.pos:
            raise ValueError("Mini: not started yet. Call `move_to` to indicate where to start the proof.")
        mp.pack('\\print', self.repl.cout)
        self.repl.cout.flush()
        return REPL.Client._parse_control_(self.repl.unpack.unpack())

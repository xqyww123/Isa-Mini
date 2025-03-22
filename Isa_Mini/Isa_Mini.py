import msgpack as mp
import IsaREPL as REPL

class Mini:
    """
    A REPL client for Isabelle/Mini
    """

    VERSION='0.1.0'

    def __run(self):
        self.repl.run_app("Minilang-REPL")
        REPL.Client._parse_control_ (self.repl.unpack.unpack())

    def __turn_off (self):
        if self.pos:
            mp.pack ("\\close", self.repl.cout)
            self.repl.cout.flush()
            return REPL.Client._parse_control_ (self.repl.unpack.unpack())

    def __init__(self, addr, thy_qualifier, initial_pos = None):
        """
        Argument repl: a REPL client

        The REPL session will turn into Minilang mode, and return into the usual
        mode until this Mini instance is explicitly closed by the `close` method.
        A Mini intance can be created only when the REPL session is at a proof state.

        Before the REPL session turns into the usual mode, any method of the REPL
        client should not be called!

        :param initial_pos: Optional position (file,line,offset) from which the Mini
        instance will start.
        """

        self.repl = REPL.Client(addr, thy_qualifier)
        self.repl.set_trace(False)
        try:
            self.repl._initialized_mini_
        except AttributeError:
            self.repl.load_theory (['Minilang_REPL.Minilang_Top'])
            self.repl.add_lib (["Minilang.Minilang_Base"])
            self.repl.run_ML ("Minilang_REPL.Minilang_Top",
                """REPL_Server.register_app "Minilang-REPL" Minilang_Top.REPL_App""")
            self.repl._initialized_mini_ = True
        self.repl.record_state ("mini-init")
        if initial_pos:
            self.repl.eval_file(initial_pos[0], initial_pos[1], initial_pos[2])
        self.pos = initial_pos
        if self.pos:
            self.__run()

    def close(self):
        """
        Give up the ongoing proof, clos the Mini instance,
        and turns the REPL session into the usual mode.
        :return: None
        """
        return self.__turn_off()

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

    def move_to (self, file, line, offset=0):
        self.__turn_off()
        self.repl.rollback ('mini-init')
        self.repl.eval_file (file, line, offset)
        self.pos = (file, line, offset)
        self.__run()

    def set_theory_and_goal(self, src):
        self.__turn_off()
        self.repl.rollback('mini-init')
        self.repl.eval(src)
        self.pos = ("#REPL", 0, 0)
        self.__run()

    def set_timeout(self, timeout):
        """
        Sets the timeout for evaluation
        
        Args:
            timeout: An integer representing timeout in seconds, or None for no timeout
        """
        if timeout is not None and not isinstance(timeout, int):
            raise TypeError("Timeout must be an integer or None")
        
        mp.pack("\\timeout", self.repl.cout)
        mp.pack(timeout, self.repl.cout)
        self.repl.cout.flush()
        return REPL.Client._parse_control_(self.repl.unpack.unpack())
    
    def eval (self, src):
        """
        Evaluates the given source Minilang code.
        The given source can contain multiple commands.
        Returns the list of the respective proof states after evaluating each of the command.
        """
        if not self.pos:
            raise ValueError("Mini: not started yet. Call `move_to` to indicate where to start the proof.")
        mp.pack (src, self.repl.cout)
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
        mp.pack('\print', self.repl.cout)
        self.repl.cout.flush()
        return REPL.Client._parse_control_(self.repl.unpack.unpack())

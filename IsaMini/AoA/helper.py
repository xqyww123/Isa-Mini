def alpha_to_num(s: str) -> int:
    """
    Convert an alphabetic string to a number in base-26 (1-indexed).
    A=1, B=2, ..., Z=26, AA=27, AB=28, ..., AZ=52, BA=53, ..., ZZ=702, AAA=703, ...
    
    Single letters cover 1-26, double letters cover 27-702, triple letters cover 703-18278, and so on.
    """
    if s == "a":
        return 0
    s = s.upper()
    n = len(s)
    # offset = 26^1 + 26^2 + ... + 26^(n-1) = (26^n - 26) / 25
    offset = (26**n - 26) // 25
    # Compute base-26 value
    value = 0
    for c in s:
        value = value * 26 + (ord(c) - ord('A'))
    return offset + value + 1


def num_to_alpha(n: int) -> str:
    """
    Convert a number to an alphabetic string (inverse of alpha_to_num, 1-indexed).
    1=A, 2=B, ..., 26=Z, 27=AA, 28=AB, ..., 52=AZ, 53=BA, ..., 702=ZZ, 703=AAA, ...
    """
    if n < 0:
        raise ValueError(f"n must be non-negative, got {n}")
    if n == 0:
        return "a"
    
    n = n - 1  # Convert to 0-indexed for internal calculation
    
    # Determine the number of letters based on thresholds: 26, 702, 18278, ...
    num_digits = 1
    threshold = 26
    while n >= threshold:
        num_digits += 1
        threshold = (26**(num_digits + 1) - 26) // 25
    
    # Subtract offset and convert remainder to base-26
    offset = (26**num_digits - 26) // 25
    remainder = n - offset
    
    result = []
    for _ in range(num_digits):
        remainder, r = divmod(remainder, 26)
        result.append(chr(ord('A') + r))
    return ''.join(reversed(result))

def split_id_into_segs(id: str) -> list[int]:
    """
    Split a string into consecutive segments of digits and letters.
    For round-trip with cat_segs_into_id, the string should start with digits.
    e.g. '11AA22AB3AC' -> [11, 27, 22, 28, 3, 29]
    """
    segs = []
    i = 0
    n = len(id)
    while i < n:
        start = i
        if id[i].isalpha():
            while i < n and id[i].isalpha():
                i += 1
            segs.append(alpha_to_num(id[start:i]))
        elif id[i].isdigit():
            while i < n and id[i].isdigit():
                i += 1
            segs.append(int(id[start:i]))
        else:
            # Non-alphanumeric character, treat as a separate segment
            i += 1
    return segs

def cat_segs_into_id(segs: list[int]) -> str:
    """
    Concatenate segments back into an ID string (inverse of split_id_into_segs).
    Alternates between digit and alpha segments, starting with digits.
    e.g. [11, 27, 22, 28, 3, 29] -> '11AA22AB3AC'
    """
    result = []
    for i, seg in enumerate(segs):
        if i % 2 == 0:
            # Even index: digit segment
            result.append(str(seg))
        else:
            # Odd index: alpha segment
            result.append(num_to_alpha(seg))
    return ''.join(result)

def incr_id_minor(id : str) -> str:
    segs = split_id_into_segs(id)
    segs[-1] += 1
    return cat_segs_into_id(segs)

def incr_id_major(id : str) -> str:
    segs = split_id_into_segs(id)
    return cat_segs_into_id([segs[0] + 1])

def _segs_between(lo: list[int], hi: list[int]) -> list[int]:
    """A segment list strictly between `lo` and `hi` in the id order (lists of
    non-negative ints compared lexicographically, where a proper prefix sorts
    BEFORE its extensions). Caller passes `lo < hi`. The result is biased to end
    in a `1` segment so it keeps room on both sides for future insertions.

    TOTAL by design — it never raises. The id order is dense *except* when `hi`
    equals `lo` followed by only zeros (e.g. lo=[0,1], hi=[0,1,0]): no key exists
    strictly between them. No id this scheme generates is ever zero-tailed (every
    generator — incr_id_*, the front-insert branch, and this function — ends in a
    segment >= 1), so that case is unreachable in practice. Should it ever arise,
    we still return a deterministic value > lo rather than raise: an uncaught
    error here would escape `insert_before`'s no-raise contract and kill the
    single-process MCP host (`call_tool` ends in `sys.exit(1)`)."""
    out: list[int] = []
    i = 0
    while True:
        l = lo[i] if i < len(lo) else None
        h = hi[i] if i < len(hi) else None
        if l is None:
            # lo exhausted: `out` == lo so far; extend to land below hi.
            if h is None:          # hi also exhausted (only via the zero-descent below)
                out.append(1); return out
            if h >= 1:
                out += [0, 1]; return out
            out.append(0); i += 1; continue   # h == 0: descend, hi tail still bounds us
        if h is None:
            # hi exhausted while lo continues (only reachable on a lo>hi misuse).
            out.append(l + 1); return out
        if l == h:
            out.append(l); i += 1; continue   # shared prefix, descend
        if h - l >= 2:
            out.append(l + 1); return out      # room between l and h
        # adjacent (h == l + 1): keep l, then exceed lo's tail (now unbounded above)
        out.append(l); i += 1
        nxt = lo[i] if i < len(lo) else None
        out.append(1 if nxt is None else nxt + 1); return out

def local_step_between(prev: str, before: str) -> str:
    """A fresh local-step strictly between two existing adjacent siblings `prev`
    and `before` (with `prev < before` in proof order).

    The first branch reproduces the historical id formula verbatim and is
    returned UNCHANGED whenever it already yields a strictly-between id — this is
    a byte-compatibility shim, not an optimization: it keeps every previously
    generated id (and thus every golden) identical. `_segs_between` is the actual
    specification and the only correct path for the cases the old formula got
    wrong (it returned an id equal to / past `before` when `before` had no
    fractional gap above `prev`, e.g. prev=`0A`, before=`0A1` -> `0A1`, a
    collision). DO NOT delete the fast path as a redundant branch — that would
    move goldens."""
    p = split_id_into_segs(prev)
    b = split_id_into_segs(before)
    if len(p) > len(b):
        cand = p[:len(b) + 1]
        cand[-1] += 1
    else:
        cand = p + [1]
    if p < cand < b:
        return cat_segs_into_id(cand)
    return cat_segs_into_id(_segs_between(p, b))


from typing import TextIO, Optional
import io


class MyIO:
    """
    A wrapper around TextIO that automatically tracks the current line number.

    Line Numbering Semantics:
    - The line counter starts at 1 (first line)
    - Each newline character ('\\n') moves the write head to the NEXT line
    - current_line() returns the line number where the write head is positioned
    - Writing text without a newline keeps the write head on the same line

    This wrapper delegates all operations to the underlying TextIO object
    while maintaining the line count.

    Example usage:
        with open('output.txt', 'w') as f:
            wrapper = MyIO(f)
            print(wrapper.current_line())     # prints: 1 (initial position)

            wrapper.write("First line\\n")    # writes to line 1, moves to line 2
            print(wrapper.current_line())     # prints: 2

            wrapper.write("Second line\\n")   # writes to line 2, moves to line 3
            print(wrapper.current_line())     # prints: 3

            wrapper.write("Third line")       # writes to line 3, stays on line 3
            print(wrapper.current_line())     # prints: 3

            wrapper.write("\\nFourth line\\n") # moves to line 4, writes, moves to line 5
            print(wrapper.current_line())     # prints: 5
    """

    def __init__(self, wrapped: TextIO, initial_line: int = 1):
        """
        Initialize the wrapper.

        Args:
            wrapped: The underlying TextIO object to wrap
            initial_line: The starting line number (default: 1)
        """
        self._wrapped = wrapped
        self._line_number = initial_line

    def write(self, s: str) -> int:
        """
        Write string to the underlying stream and update line counter.

        Args:
            s: The string to write

        Returns:
            The number of characters written
        """
        # Count newlines in the string
        newline_count = s.count('\n')
        self._line_number += newline_count

        # Delegate to the wrapped object
        return self._wrapped.write(s)

    def writelines(self, lines: list[str]) -> None:
        """
        Write a list of strings to the underlying stream.

        Args:
            lines: List of strings to write
        """
        for line in lines:
            self.write(line)

    def current_line(self) -> int:
        """
        Get the current line number (where the write head is positioned).

        The line number represents which line the next character will be written to.
        After writing "text\\n", the write head moves to the next line, so
        current_line() will return the line number AFTER the newline.

        Returns:
            The current line number (1-indexed)
        """
        return self._line_number

    def reset_line_counter(self, line: int = 1) -> None:
        """
        Reset the line counter to a specific value.

        Args:
            line: The line number to reset to (default: 1)
        """
        self._line_number = line

    # Delegate all other methods to the wrapped object
    def __getattr__(self, name):
        """Delegate any undefined methods to the wrapped TextIO object."""
        return getattr(self._wrapped, name)

    def __enter__(self):
        """Support context manager protocol."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Support context manager protocol."""
        if hasattr(self._wrapped, '__exit__'):
            return self._wrapped.__exit__(exc_type, exc_val, exc_tb)
        return False

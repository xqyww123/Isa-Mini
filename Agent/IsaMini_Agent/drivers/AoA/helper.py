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

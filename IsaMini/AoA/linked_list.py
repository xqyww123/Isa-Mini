"""Immutable singly-linked list.

Provides a minimal cons-cell linked list for use where O(1) head/tail
destructure matters (e.g. the proof-op parsing pipeline in model.py).

Python has no native analog: `collections.deque` is a block-array
double-ended queue and doesn't give cons-cell semantics;
`pyrsistent.PList` is a third-party dependency.  Rolling our own here
is ~20 lines.

A linked list is `Cons[T] | None`:
  - `None` — the empty list (nil).
  - `Cons(head, tail)` — a non-empty cell.

All operations are pure; no mutation.  Match-patterns work with keyword
fields::

    match xs:
        case None: ...
        case Cons(head=h, tail=t): ...

Derived operations are intentionally left to callers as one-liners::

    list(iterate(xs))            # materialize to list
    sum(1 for _ in iterate(xs))  # length
    xs is None                   # is_empty
"""

from dataclasses import dataclass
from typing import Iterable, Iterator


@dataclass(frozen=True, slots=True)
class Cons[T]:
    head: T
    tail: 'Cons[T] | None'


type LinkedList[T] = Cons[T] | None


def from_iterable[T](items: Iterable[T]) -> LinkedList[T]:
    """Build a linked list from an iterable, preserving order:
    ``from_iterable([a, b, c]) == Cons(a, Cons(b, Cons(c, None)))``."""
    buf = list(items)
    r: LinkedList[T] = None
    for x in reversed(buf):
        r = Cons(x, r)
    return r


def iterate[T](xs: LinkedList[T]) -> Iterator[T]:
    """Iterate from head to tail.  Handles ``None`` (empty) gracefully."""
    while xs is not None:
        yield xs.head
        xs = xs.tail


def concat[T](a: LinkedList[T], b: LinkedList[T]) -> LinkedList[T]:
    """Concatenate ``a ++ b`` into a new list.  ``b`` is shared by
    reference from the tail position (safe: all cells are immutable).
    Iterative — safe for any length of ``a``."""
    if a is None:
        return b
    # Walk `a` collecting heads (O(len(a))), then rebuild from b up.
    heads: list[T] = []
    cur = a
    while cur is not None:
        heads.append(cur.head)
        cur = cur.tail
    result: LinkedList[T] = b
    for h in reversed(heads):
        result = Cons(h, result)
    return result

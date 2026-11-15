"""Reference RASP programs for the transformer task set (ground truth for training data
and for the I/O-only control). Written against xf.rasp, which mirrors tracr.rasp names."""
from __future__ import annotations

from xf.rasp import (Aggregate, Comparison, Map, Select, SelectorWidth, SequenceMap, indices,
                     numerical, tokens)


def length():
    return SelectorWidth(Select(tokens, tokens, Comparison.TRUE))


def reverse():
    opp = SequenceMap(lambda i, n: n - i - 1, indices, length())
    return Aggregate(Select(indices, opp, Comparison.EQ), tokens)


def hist():
    """For each position, how many times its token occurs in the sequence."""
    return SelectorWidth(Select(tokens, tokens, Comparison.EQ))


def sort_unique():
    """Sort a sequence of distinct tokens (ascending)."""
    smaller = SelectorWidth(Select(tokens, tokens, Comparison.LT))
    return Aggregate(Select(smaller, indices, Comparison.EQ), tokens)


def frac_prevs(target="a"):
    """Fraction of positions <= i whose token is `target` (numerical)."""
    is_t = numerical(Map(lambda t: 1 if t == target else 0, tokens))
    return numerical(Aggregate(Select(indices, indices, Comparison.LEQ), is_t, default=0))


def most_frequent():
    """At every position, the token that occurs most often (ties -> smallest token):
    sort tokens by (-count, token) via a key that is unique per (count, token) pair."""
    key = SequenceMap(lambda c, t: -c * 100 + ord(str(t)[0]), hist(), tokens)
    rank = SelectorWidth(Select(key, key, Comparison.LT))
    return Aggregate(Select(rank, Map(lambda _: 0, indices), Comparison.EQ), tokens)


def dyck1_prefix_balanced():
    """Per position: 1 if the prefix up to i has equally many '(' and ')' (count balance
    only; it does not check that the prefix never went negative)."""
    sign = numerical(Map(lambda t: 1 if t == "(" else -1, tokens))
    run = numerical(Aggregate(Select(indices, indices, Comparison.LEQ), sign, default=0))
    return Map(lambda v: 1 if abs(v) < 1e-9 else 0, run)


TASKS = {
    "reverse": dict(prog=reverse, vocab=list("abcde"), unique=False),
    "hist": dict(prog=hist, vocab=list("abcd"), unique=False),
    "sort_unique": dict(prog=sort_unique, vocab=list("abcdefgh"), unique=True),
    "frac_prevs": dict(prog=frac_prevs, vocab=list("abc"), unique=False),
    "most_frequent": dict(prog=most_frequent, vocab=list("abcd"), unique=False),
    "dyck1_balanced": dict(prog=dyck1_prefix_balanced, vocab=list("()"), unique=False),
}

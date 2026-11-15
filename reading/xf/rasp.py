"""Minimal RASP interpreter with Tracr-compatible names (tracr.rasp.rasp API subset).

A doctor writes a program against these names; the same source runs here (for scoring
functional agreement) and, unchanged, under tracr (for compilation) if tracr is installed.

    from xf.rasp import *
    length = SelectorWidth(Select(tokens, tokens, Comparison.TRUE))
    opp = SequenceMap(lambda i, n: n - i - 1, indices, length)
    reverse = Aggregate(Select(indices, opp, Comparison.EQ), tokens)
    evaluate(reverse, ["a", "b", "c"])  ->  ["c", "b", "a"]

Semantics follow Tracr: Select(keys, queries, cmp) selects key position k for query
position q when cmp(key=keys[k], query=queries[q]); Comparison.LT means key < query.
Aggregate is categorical by default (all selected values must agree, else None) and
numerical (mean of selected values, default if none) when wrapped in numerical().
"""
from __future__ import annotations

import enum
from typing import Any, Callable

__all__ = ["tokens", "indices", "Map", "SequenceMap", "Select", "Aggregate", "SelectorWidth",
           "Comparison", "numerical", "categorical", "Full", "ConstantSOp", "SelectorAnd",
           "SelectorOr", "SelectorNot", "evaluate"]


class Comparison(enum.Enum):
    EQ = "EQ"
    LT = "LT"
    LEQ = "LEQ"
    GT = "GT"
    GEQ = "GEQ"
    NEQ = "NEQ"
    TRUE = "TRUE"
    FALSE = "FALSE"

    def __call__(self, key, query) -> bool:
        if self is Comparison.TRUE:
            return True
        if self is Comparison.FALSE:
            return False
        if key is None or query is None:
            return False
        return {"EQ": key == query, "LT": key < query, "LEQ": key <= query, "GT": key > query,
                "GEQ": key >= query, "NEQ": key != query}[self.value]


class SOp:
    encoding = "categorical"

    def eval(self, xs: list) -> list:
        raise NotImplementedError

    def named(self, name: str):
        self.label = name
        return self

    # tracr-style arithmetic sugar is not supported on purpose: use Map / SequenceMap.


class _Tokens(SOp):
    def eval(self, xs):
        return list(xs)


class _Indices(SOp):
    def eval(self, xs):
        return list(range(len(xs)))


tokens = _Tokens()
indices = _Indices()


class Map(SOp):
    def __init__(self, f: Callable, inner: SOp, simplify: bool = True):
        self.f, self.inner = f, inner

    def eval(self, xs):
        return [None if v is None else self.f(v) for v in self.inner.eval(xs)]


class SequenceMap(SOp):
    def __init__(self, f: Callable, a: SOp, b: SOp):
        self.f, self.a, self.b = f, a, b

    def eval(self, xs):
        return [None if (x is None or y is None) else self.f(x, y)
                for x, y in zip(self.a.eval(xs), self.b.eval(xs))]


class Full(SOp):
    def __init__(self, value: Any):
        self.value = value

    def eval(self, xs):
        return [self.value] * len(xs)


ConstantSOp = Full


class Selector:
    def matrix(self, xs) -> list[list[bool]]:
        raise NotImplementedError


class Select(Selector):
    def __init__(self, keys: SOp, queries: SOp, predicate: Comparison):
        self.keys, self.queries, self.predicate = keys, queries, predicate

    def matrix(self, xs):
        k, q = self.keys.eval(xs), self.queries.eval(xs)
        return [[bool(self.predicate(kk, qq)) for kk in k] for qq in q]


class SelectorAnd(Selector):
    def __init__(self, a, b):
        self.a, self.b = a, b

    def matrix(self, xs):
        return [[x and y for x, y in zip(r, s)] for r, s in zip(self.a.matrix(xs), self.b.matrix(xs))]


class SelectorOr(SelectorAnd):
    def matrix(self, xs):
        return [[x or y for x, y in zip(r, s)] for r, s in zip(self.a.matrix(xs), self.b.matrix(xs))]


class SelectorNot(Selector):
    def __init__(self, a):
        self.a = a

    def matrix(self, xs):
        return [[not x for x in r] for r in self.a.matrix(xs)]


class Aggregate(SOp):
    def __init__(self, selector: Selector, sop: SOp, default: Any = None):
        self.selector, self.sop, self.default = selector, sop, default

    def eval(self, xs):
        m, vals = self.selector.matrix(xs), self.sop.eval(xs)
        out = []
        for row in m:
            sel = [v for v, s in zip(vals, row) if s]
            if not sel:
                out.append(self.default)
            elif self.encoding == "numerical":
                out.append(sum(sel) / len(sel) if all(isinstance(v, (int, float)) for v in sel) else None)
            else:
                out.append(sel[0] if all(v == sel[0] for v in sel) else None)
        return out


class SelectorWidth(SOp):
    def __init__(self, selector: Selector):
        self.selector = selector

    def eval(self, xs):
        return [sum(row) for row in self.selector.matrix(xs)]


def numerical(sop: SOp) -> SOp:
    sop.encoding = "numerical"
    return sop


def categorical(sop: SOp) -> SOp:
    sop.encoding = "categorical"
    return sop


def evaluate(program: SOp, xs: list) -> list:
    return program.eval(list(xs))

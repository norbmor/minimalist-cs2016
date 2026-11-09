"""
extensions.py -- Extension 1: selectional Merge.

Collins & Stabler's Triggered Merge (D27) checks only the trigger / no-trigger
asymmetry: Merge(A,B) is defined iff Triggers(A) is non-empty and Triggers(B)
is empty.  Nothing requires the trigger feature to *match* B.  The paper's
example (14) writes selection features as [__vP] and says T "takes a vP
complement", but that matching is commentary, not part of any definition, and
section 7 explicitly leaves open "how trigger features impose category
constraints".

This module adds the matching as an explicit extension, in two forms --
with trigger features ranked (a head selects its complement before its
specifier) and unranked, as the paper assumes ("We do not assume that the
trigger features of (14a,b) are ordered") -- and measures what each does by
enumerating every complete derivation (D15) a lexical array admits.

Nothing here is attributed to the paper.
"""
from __future__ import annotations

import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from contextlib import contextmanager
from typing import Any, Dict, FrozenSet, List, Optional, Sequence, Tuple

import cs2016 as cs
from cs2016 import (
    Feature, LIToken, Lexicon, SO, Stage, label, satisfies_extension,
    satisfies_ntc, select, triggered_merge, triggers,
    is_binary_branching, unique_root_occurrences, _all_contained,
)


# ---------------------------------------------------------------------
# The extension
# ---------------------------------------------------------------------

def category_features(B: SO) -> FrozenSet[str]:
    """The non-trigger syntactic features of the label of B (D28)."""
    return frozenset(f.name for f in label(B).li.syn if not f.trigger)


def satisfies_selection(tf: Feature, B: SO, epp_requires: Optional[str] = None) -> bool:
    """Does B satisfy the trigger feature tf?

    __X  is satisfied by a B whose label carries the category feature X.
    OP   is satisfied by a B whose label carries the feature OP.
    EPP  imposes no categorial requirement (the paper's (14a): T "requires a
         specifier"), unless `epp_requires` names one.
    """
    if tf.name.startswith("__"):
        return tf.name[2:] in category_features(B)
    if tf.name == "OP":
        return "OP" in category_features(B)
    if tf.name == "EPP" and epp_requires is not None:
        return epp_requires in category_features(B)
    return True


def make_selectional_merge(epp_requires: Optional[str] = None, ordered: bool = True):
    """Triggered Merge (D27) plus feature matching.

    ordered=True:  the trigger feature checked is the lowest-ranked one
                   (cs2016.DISCHARGE's default), and it must match B.
    ordered=False: Merge(A,B) is defined if *some* trigger feature of A
                   matches B, and that is the one checked -- "a particular
                   one, determined by B and C" (D26).  Run it inside
                   `unordered_triggers()` so that Triggers agrees.
    """
    def rule(A: SO, B: SO) -> FrozenSet[SO]:
        m = triggered_merge(A, B)      # raises on the D27 conditions first
        tfs = triggers(A)
        ok = (satisfies_selection(tfs[0], B, epp_requires) if ordered
              else any(satisfies_selection(tf, B, epp_requires) for tf in tfs))
        if not ok:
            raise ValueError(
                f"selection failure: {[t.name for t in tfs]} not satisfied by a "
                f"{sorted(category_features(B))} phrase "
                "(extension, not Collins & Stabler 2016)")
        return m
    rule.__name__ = ("selectional_merge" + ("" if ordered else "_unordered")
                     + (f"_epp_{epp_requires}" if epp_requires else ""))
    return rule


selectional_merge = make_selectional_merge()


def _matching_discharge(tfs: Tuple[Feature, ...], C: SO) -> Feature:
    """D26(ii) with the checked feature determined by C: the lowest-ranked
    trigger feature that C satisfies (falling back to the lowest-ranked)."""
    for tf in tfs:
        try:
            if satisfies_selection(tf, C):
                return tf
        except ValueError:
            continue
    return tfs[0]


@contextmanager
def unordered_triggers():
    """Temporarily make Triggers (D26) check the feature that C satisfies."""
    old = cs.DISCHARGE
    cs.DISCHARGE = _matching_discharge
    try:
        yield
    finally:
        cs.DISCHARGE = old


# ---------------------------------------------------------------------
# Enumerating the derivations a lexical array admits
# ---------------------------------------------------------------------

def successors(s: Stage, merge_rule) -> List[Stage]:
    """Every stage S2 such that S derives S2 by Select or Merge (D14iii)."""
    out: List[Stage] = []
    for li in s.la:
        out.append(select(li, s))
    for A in s.w:
        if not isinstance(A, frozenset) and not triggers(A):
            continue
        candidates = [B for B in s.w if B != A] + _all_contained(A)
        for B in candidates:
            if A == B:
                continue
            try:
                m = merge_rule(A, B)
            except ValueError:
                continue
            out.append(Stage(s.la, (s.w - {A, B}) | {m}))
    seen, uniq = set(), []
    for s2 in out:
        if s2 not in seen:
            seen.add(s2)
            uniq.append(s2)
    return uniq


def explore(la: FrozenSet[LIToken], merge_rule, max_states: int = 200_000
            ) -> Tuple[int, FrozenSet[SO], int]:
    """Count the derivations from `la` that end in LA_n = {}, W_n = {A} (D15).

    Returns (number of distinct derivations, set of final syntactic objects,
    number of distinct stages visited).  The state graph is finite and acyclic:
    Select strictly shrinks the lexical array and each Merge checks exactly
    one trigger feature (D26ii, D27).
    """
    memo: Dict[Stage, Tuple[int, FrozenSet[SO]]] = {}

    def walk(s: Stage) -> Tuple[int, FrozenSet[SO]]:
        if s in memo:
            return memo[s]
        if len(memo) > max_states:
            raise RuntimeError("state cap exceeded")
        memo[s] = (0, frozenset())           # provisional, graph is acyclic
        n, finals = 0, set()
        if not s.la and len(s.w) == 1:       # D15
            n += 1
            finals.add(next(iter(s.w)))
        for s2 in successors(s, merge_rule):
            n2, f2 = walk(s2)
            n += n2
            finals |= f2
        memo[s] = (n, frozenset(finals))
        return memo[s]

    start = Stage(la, frozenset())
    n, finals = walk(start)
    return n, finals, len(memo)


def theorems_hold_everywhere(la: FrozenSet[LIToken], merge_rule,
                             max_states: int = 200_000) -> Dict[str, bool]:
    """Check T5, T6, T8, T9 on every stage and transition reachable from `la`."""
    seen: set = set()
    res = {"T5 binary branching": True, "T6 unique root occurrences": True,
           "T8 No Tampering": True, "T9 Extension (at Merge)": True}
    stack = [Stage(la, frozenset())]
    while stack:
        s = stack.pop()
        if s in seen:
            continue
        seen.add(s)
        if len(seen) > max_states:
            raise RuntimeError("state cap exceeded")
        res["T6 unique root occurrences"] &= unique_root_occurrences(s.w)
        res["T5 binary branching"] &= all(is_binary_branching(x) for x in s.w)
        for s2 in successors(s, merge_rule):
            res["T8 No Tampering"] &= satisfies_ntc(s, s2)
            if s2.la == s.la:                       # a Merge step
                res["T9 Extension (at Merge)"] &= satisfies_extension(s, s2)
            stack.append(s2)
    return res


RULES = (
    ("D27 Triggered Merge", lambda: triggered_merge, False),
    ("+ selection (ranked triggers)", lambda: selectional_merge, False),
    ("+ selection (ranked), EPP needs D", lambda: make_selectional_merge("D"), False),
    ("+ selection (unranked triggers)", lambda: make_selectional_merge(ordered=False), True),
    ("+ selection (unranked), EPP needs D",
     lambda: make_selectional_merge("D", ordered=False), True),
)


def compare(lex: Lexicon, la: Sequence[LIToken], rules=RULES) -> Dict[str, Any]:
    """Run a lexical array under each Merge rule in `rules`."""
    la = frozenset(la)
    out: Dict[str, Any] = {}
    for name, make, unordered in rules:
        rule = make()
        if unordered:
            with unordered_triggers():
                n, finals, states = explore(la, rule)
                thms = theorems_hold_everywhere(la, rule)
                pfs = _pf_strings(finals)
        else:
            n, finals, states = explore(la, rule)
            thms = theorems_hold_everywhere(la, rule)
            pfs = _pf_strings(finals)
        out[name] = {"derivations": n, "distinct complete objects": len(finals),
                     "stages visited": states, "theorems": thms, "finals": finals,
                     "pf strings": pfs}
    return out


def _pf_strings(finals) -> List[str]:
    """Distinct PF strings of the complete objects, each spelled out as a
    phase of its own (D41 with Phase = the object)."""
    out = set()
    for X in finals:
        try:
            out.add(cs.linear_order(X))
        except ValueError:
            pass
    return sorted(out)


if __name__ == "__main__":
    import time
    from derivations import LEX
    T = LEX.token
    la = [T("see", 1), T("Chris", 2), T("v*", 3), T("John", 4), T("T", 5), T("Comp", 6)]
    for name, make, unordered in RULES:
        t0 = time.time()
        r = compare(LEX, la, rules=((name, make, unordered),))[name]
        print(f"{name:40} {r['derivations']:>10,} {r['distinct complete objects']:>5} "
              f"{r['stages visited']:>6} {len(r['pf strings']):>3} "
              f"{all(r['theorems'].values())}  {time.time() - t0:.1f}s")
        print("    ", r["pf strings"])

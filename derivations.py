"""
derivations.py -- the worked examples of Collins & Stabler (2016), run through
the axiomatization in cs2016.py, plus a few derivations added to exercise it.

Each function returns a validated `Derivation`.  Numbers in parentheses are the
paper's example numbers (2016 journal version).
"""
from __future__ import annotations

# This project is a set of plain modules, not an installed package, so it
# relies on its own directory being importable.  Under PYTHONSAFEPATH=1
# (equivalently `python -P`) the script directory is not added to sys.path,
# and the imports below would fail; put it back.
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)


from typing import Optional

from cs2016 import (
    Derivation, LexicalItem, Lexicon, LIToken, NTCDerivation, SO,
    complement_of, contains, converges_at_ci, converges_at_sm, fmt_lf,
    labelled_bracket, merge, pf_string, pho, positions, sem, syn, transfer_lf,
    transfer_pf, trig, universal_grammar, ILanguage, _brief,
)

# ---------------------------------------------------------------------
# A lexicon (D3).  Trigger features (D25) are ranked left to right: selection
# first, then EPP / OP.  The paper does not order trigger features, and under
# D26/D27 the rank never affects what is derivable (see cs2016.DISCHARGE).
#
# Selection features are written __X; the axioms do not check them (D27 checks
# only the trigger / no-trigger asymmetry), but extensions.py can.  Following
# the paper's (14), the tense head is T and its phrase TP.
# ---------------------------------------------------------------------

LEX = Lexicon({
    LexicalItem(sem("JOHN"), syn("D"), pho("John"), "John", "D"),
    LexicalItem(sem("CHRIS"), syn("D"), pho("Chris"), "Chris", "D"),
    LexicalItem(sem("YOU"), syn("D"), pho("you"), "you", "D"),
    LexicalItem(sem("WHO"), syn("D", "OP"), pho("who"), "who", "D"),
    LexicalItem(sem("SEE"), syn("V") | trig("__D"), pho("see"), "see", "V"),
    # (15): "a lexical item token see has two trigger features"
    LexicalItem(sem("SEE"), syn("V") | trig("__D", "EPP"), pho("see"), "see_2TF", "V"),
    LexicalItem(sem("FALL"), syn("V") | trig("__D"), pho("fell"), "fall", "V"),
    LexicalItem(sem("WIN"), syn("V"), pho("win"), "win", "V"),
    LexicalItem(sem("THINK"), syn("V") | trig("__Comp"), pho("think"), "think", "V"),
    LexicalItem(frozenset(), syn("v*") | trig("__V", "EPP"), (), "v*", "v"),
    LexicalItem(frozenset(), syn("v*") | trig("__V", "EPP", "OP"), (), "v*_edge", "v"),
    LexicalItem(frozenset(), syn("T") | trig("__v*", "EPP"), (), "T", "T"),
    LexicalItem(frozenset(), syn("T") | trig("__V", "EPP"), (), "T_V", "T"),
    LexicalItem(frozenset(), syn("T") | trig("__V", "EPP"), pho("to"), "to", "T"),
    # `will` takes a vP complement: its subject is the external argument of v*
    LexicalItem(frozenset(), syn("T") | trig("__v*", "EPP"), pho("will"), "will", "T"),
    LexicalItem(frozenset(), syn("T") | trig("__Deg", "EPP"), pho("is"), "is", "T"),
    LexicalItem(frozenset(), syn("A") | trig("__T"), pho("likely"), "likely", "A"),
    LexicalItem(frozenset(), syn("Deg", "OP") | trig("__A"), pho("how"), "how", "Deg"),
    LexicalItem(frozenset(), syn("Comp") | trig("__T"), (), "Comp", "C"),
    LexicalItem(frozenset(), syn("Comp") | trig("__T", "OP"), (), "Comp_Q", "C"),
    # an overt complementizer with an edge feature, for the paper's (21)
    LexicalItem(frozenset(), syn("Comp") | trig("__T", "OP"), pho("that"), "that", "C"),
    # A lexical item carrying a semantic feature that the CI interface cannot
    # read; used to exhibit a crashing derivation (D42).
    LexicalItem(sem("CHRIS", "uCase", uninterpretable=("uCase",)),
                syn("D"), pho("Chris"), "Chris_uCase", "D"),
})

IL = ILanguage(LEX, universal_grammar(LEX))
T = LEX.token


# ---------------------------------------------------------------------
# Section 3, before labels: Merge is D13, with no triggering condition.
# ---------------------------------------------------------------------

def external_merge_6(cls=Derivation) -> Derivation:
    """(4), derived as in (6)/(8): {John2, {see1, John1}} -- two tokens of John."""
    d = cls(LEX, [T("John", 2), T("see", 1), T("John", 1)], merge_rule=merge)
    d.select("John", 1)                      # S2
    d.select("see", 1)                       # S3
    d.merge_roots()                          # S4  Merge(see1, John1)
    d.select("John", 2)                      # S5
    d.merge_roots()                          # S6  Merge(John2, {see1, John1})
    return d


def internal_merge_7(cls=Derivation) -> Derivation:
    """(2), derived as in (7): {John1, {see1, John1}} -- one token, two occurrences."""
    d = cls(LEX, [T("see", 1), T("John", 1)], merge_rule=merge)
    d.select("John", 1)
    d.select("see", 1)
    d.merge_roots()                          # {see1, John1}
    d.internal_merge(T("John", 1))           # {John1, {see1, John1}}
    return d


# ---------------------------------------------------------------------
# (15)  A token with two trigger features: the same structure as (2), built
#       by Triggered Merge (D27), checking one trigger feature per Merge.
# ---------------------------------------------------------------------

def two_trigger_features_15(cls=Derivation) -> Derivation:
    d = cls(LEX, [T("John", 1), T("see_2TF", 2)])
    d.select("John", 1)                      # (15a)
    d.select("see_2TF", 2)                   # (15b)
    d.merge_roots()                          # (15c) Merge(see2, John1)
    d.internal_merge(T("John", 1))           # (15d) Merge({John1, see2}, John1)
    return d                                 # (15e)


# ---------------------------------------------------------------------
# (16)/(17)  [VP see Chris]  -- a derivation with no Transfer.  The paper's
#            TransferLF / TransferPF of it relative to a vP phase are shown
#            in `report()` using `john_sees_chris`, which has that phase.
# ---------------------------------------------------------------------

def vp_see_chris(cls=Derivation) -> Derivation:
    d = cls(LEX, [T("see", 1), T("Chris", 2)])
    d.select("see", 1)
    d.select("Chris", 2)
    d.merge_roots()
    return d


# ---------------------------------------------------------------------
# (18)  [CP Comp [TP John T [VP fell <John>]]]
#       Unaccusative A-movement; TransferPF clause (c) skips the lower John.
# ---------------------------------------------------------------------

def john_fell(cls=Derivation) -> Derivation:
    d = cls(LEX, [T("fall", 1), T("John", 2), T("T_V", 3), T("Comp", 4)])
    d.select("fall", 1)
    d.select("John", 2)
    d.merge_roots()                          # {fall1, John2}         external Merge
    d.select_and_merge("T_V", 3)             # {T3, {fall1, John2}}   external Merge
    d.internal_merge(T("John", 2))           # {John2, {T3, VP}}      internal Merge
    d.select_and_merge("Comp", 4)            # {Comp4, TP}
    d.transfer()                             # D38(a): Transfer(CP, CP)
    return d


# ---------------------------------------------------------------------
# "John sees Chris" -- a v* phase, Cyclic-Transfer of its complement (D36),
# and the Phase Impenetrability Condition (T14).  Not a paper example.
# ---------------------------------------------------------------------

def john_sees_chris(cls=Derivation) -> Derivation:
    d = cls(LEX, [T("see", 1), T("Chris", 2), T("v*", 3),
                  T("John", 4), T("T", 5), T("Comp", 6)])
    d.select("see", 1)
    d.select("Chris", 2)
    d.merge_roots()                          # VP = {see1, Chris2}
    d.select_and_merge("v*", 3)              # {v*3, VP}
    d.select_and_merge("John", 4)            # v*P = {John4, {v*3, VP}}   strong phase
    d.cyclic_transfer()                      # D36: VP -> <TransferPF, TransferLF>
    d.select_and_merge("T", 5)               # {T5, v*P}
    d.internal_merge(T("John", 4))
    d.select_and_merge("Comp", 6)
    d.transfer()
    return d


# ---------------------------------------------------------------------
# (19)/(20)  "How likely to win is John?"  -- remnant movement in one phase.
#
# D40 makes John in {John, {to, win}} non-final in *both* occurrences of the
# moved DegP, because TP contains {John, {to, win}} and has John as a member.
# Transfer applies once, at (20d); had it applied at (20c), the DegP would be
# inside the transferred TP and could not move (see the tests).
# ---------------------------------------------------------------------

def remnant_movement(cls=Derivation) -> Derivation:
    john = T("John", 1)
    d = cls(LEX, [T("win", 2), T("to", 3), john, T("likely", 4),
                  T("how", 5), T("is", 6), T("Comp_Q", 7)])
    d.select("win", 2)
    d.select_and_merge("to", 3)              # {to3, win2}
    d.select_and_merge("John", 1)            # {John1, {to3, win2}}
    d.select_and_merge("likely", 4)
    d.select_and_merge("how", 5)             # DegP = {how5, {likely4, ...}}
    d.select_and_merge("is", 6)              # (20a) is how likely John to win
    d.internal_merge(john)                   # (20b) John is how likely <John> to win
    d.select_and_merge("Comp_Q", 7)          # (20c) Comp John is ...
    d.internal_merge(_degp(d.root))          # (20d) [how likely <John> to win] John is <...>
    d.transfer()                             # Transfer(CP, CP)
    return d


def _degp(root: SO) -> SO:
    """The complement of `is` -- the remnant DegP."""
    is_ = next(t for t in _tokens(root) if t.li.name == "is")
    for p in positions(is_, root):
        if len(p) >= 2:
            c = complement_of(is_, p[-2])
            if c is not None:
                return c
    raise ValueError("no DegP")


def _tokens(X, acc=None):
    acc = set() if acc is None else acc
    if isinstance(X, LIToken):
        acc.add(X)
    elif isinstance(X, frozenset):
        for m in X:
            _tokens(m, acc)
    return acc


# ---------------------------------------------------------------------
# (21)  [CP How likely <John> to win do you [vP think [CP that John is]]]
#
# The same remnant, moved out of an embedded clause.  Under the plug-back-in
# model (D36-D38) the embedded TP is replaced by its interface pair before the
# matrix phase is spelled out, so at the matrix level nothing contains
# {John, {to, win}} and has John as a member: by D40 John is *final* inside the
# moved DegP, and TransferPF pronounces it twice.  This is the problem the
# paper calls lethal for the plug-back-in model.  Run with cls=NTCDerivation
# (section 12), the structure is intact and John is pronounced once.
#
# No head movement, so no do-support: the output has no "do".
# ---------------------------------------------------------------------

def remnant_across_phases(cls=Derivation) -> Derivation:
    john, you = T("John", 1), T("you", 10)
    d = cls(LEX, [T("win", 2), T("to", 3), john, T("likely", 4), T("how", 5),
                  T("is", 6), T("that", 7), T("think", 8), T("v*_edge", 9), you,
                  T("T", 11), T("Comp_Q", 12)])
    d.select("win", 2)
    d.select_and_merge("to", 3)
    d.select_and_merge("John", 1)
    d.select_and_merge("likely", 4)
    d.select_and_merge("how", 5)             # DegP
    d.select_and_merge("is", 6)
    d.internal_merge(john)                   # embedded TP = John is <DegP>
    d.select_and_merge("that", 7)
    degp = _degp(d.root)
    d.internal_merge(degp)                   # embedded Spec,CP
    d.cyclic_transfer()                      # embedded TP -> "John is"
    d.select_and_merge("think", 8)
    d.select_and_merge("v*_edge", 9)
    d.select_and_merge("you", 10)
    d.internal_merge(degp)                   # matrix v* edge
    d.cyclic_transfer()                      # VP -> "think that John is"
    d.select_and_merge("T", 11)
    d.internal_merge(you)
    d.select_and_merge("Comp_Q", 12)
    d.internal_merge(degp)                   # matrix Spec,CP
    d.transfer()
    return d


# ---------------------------------------------------------------------
# Successive-cyclic wh-movement -- "Who do you think John will see".  Not a
# paper example (the 2011 draft had a Cyclic-Transfer example built on this
# embedded clause; the published version does not).
#
# `John` is the external argument of `see`: it is externally merged in the
# specifier of the embedded v*P, and raises to Spec,TP of `will`.  The
# embedded v*P is a strong phase (D35) whose VP is transferred before `will`
# embeds it (D38), so `who` must first move to that v* edge.  Each phase on
# the way up is the same: at the matrix v* phase the VP containing the
# embedded CP is transferred, so `who` must already be at the matrix v* edge,
# or it is trapped (see `wh_trapped_at_the_phase_edge`).  `who` ends with five
# occurrences.  No head movement, so no do-support.
# ---------------------------------------------------------------------

def successive_cyclic_wh(cls=Derivation, escape_the_matrix_vP: bool = True,
                         stop_after_matrix_vP: bool = False) -> Derivation:
    who = T("who", 1)
    d = cls(LEX, [who, T("Comp_Q", 2), T("John", 3), T("will", 4), T("see", 5),
                  T("think", 6), T("v*_edge", 7), T("you", 8), T("T", 9),
                  T("Comp_Q", 10), T("v*_edge", 11)])
    # -- embedded clause ---------------------------------------------------
    d.select("see", 5)
    d.select_and_merge("who", 1)             # VP  = {see5, who1}
    d.select_and_merge("v*_edge", 11)        # {v*11, VP}
    d.select_and_merge("John", 3)            # {John3, {v*11, VP}}  external argument
    d.internal_merge(who)                    # v*P = {who1, ...}           edge 1
    d.cyclic_transfer()                      # complement of v*11 -> see
    d.select_and_merge("will", 4)            # {will4, v*P}
    d.internal_merge(T("John", 3))           # TP  = {John3, {will4, v*P}}
    d.select_and_merge("Comp_Q", 2)          # {Comp2, TP}
    d.internal_merge(who)                    # CP  = {who1, {Comp2, TP}}   edge 2
    d.cyclic_transfer()                      # complement of Comp2 -> John-will-see
    # -- matrix clause ----------------------------------------------------
    d.select_and_merge("think", 6)           # VP  = {think6, CP}
    d.select_and_merge("v*_edge", 7)         # {v*7, VP}
    d.select_and_merge("you", 8)             # {you8, {v*7, VP}}
    if escape_the_matrix_vP:
        d.internal_merge(who)                # v*P = {who1, ...}           edge 3
    d.cyclic_transfer()                      # complement of v*7
    if stop_after_matrix_vP:
        return d
    d.select_and_merge("T", 9)
    d.internal_merge(T("you", 8))
    d.select_and_merge("Comp_Q", 10)
    d.internal_merge(who)                    # matrix Spec,CP              landing
    d.transfer()
    return d


def wh_trapped_at_the_phase_edge() -> str:
    """Without the intermediate step to the matrix v* edge, `who` is inside the
    transferred VP when the v* phase is spelled out, and can never move again."""
    d = successive_cyclic_wh(escape_the_matrix_vP=False, stop_after_matrix_vP=True)
    who = T("who", 1)
    assert not contains(d.root, who), "who should no longer be a term of the v*P"
    try:
        d.internal_merge(who)
    except ValueError as e:
        return str(e)
    raise AssertionError("expected wh-movement out of the transferred VP to fail")


# ---------------------------------------------------------------------
# A crashing derivation (D42): an uninterpretable SEM feature survives to CI.
# ---------------------------------------------------------------------

def crashing(cls=Derivation) -> Derivation:
    d = cls(LEX, [T("see", 1), T("Chris_uCase", 2), T("v*", 3),
                  T("John", 4), T("T", 5), T("Comp", 6)])
    d.select("see", 1)
    d.select("Chris_uCase", 2)
    d.merge_roots()
    d.select_and_merge("v*", 3)
    d.select_and_merge("John", 4)
    d.cyclic_transfer()
    d.select_and_merge("T", 5)
    d.internal_merge(T("John", 4))
    d.select_and_merge("Comp", 6)
    d.transfer()
    return d


ALL = {
    "(6)/(8) external Merge, untriggered (D13)": external_merge_6,
    "(7) internal Merge, untriggered (D13)": internal_merge_7,
    "(15) two trigger features (D26, D27)": two_trigger_features_15,
    "(16)/(17) [VP see Chris]": vp_see_chris,
    "(18) John fell": john_fell,
    "John sees Chris (v* phase, T14)": john_sees_chris,
    "(19)/(20) How likely to win is John?": remnant_movement,
    "(21) remnant movement across two phases (plug-back-in)": remnant_across_phases,
    "Who do you think John will see (successive cyclicity)": successive_cyclic_wh,
    "crashing derivation (D42)": crashing,
}


def report(items: Optional[dict] = None, coda: bool = True) -> str:
    """The stage-by-stage trace of `items` (default: this module's derivations).

    `sentences.py` reuses this with its own mapping, so the report format
    lives in one place.
    """
    out = []
    for title, fn in (ALL if items is None else items).items():
        d = fn()
        out.append("=" * 74)
        out.append(title)
        out.append("=" * 74)
        out.append(d.pretty())
        final = next(iter(d.stage.w))
        out.append("")
        last_syntactic = next(
            (s.stage for s in reversed(d.steps)
             if s.op in ("Merge", "Select") and len(s.stage.w) == 1), None)
        if last_syntactic is not None:
            root = next(iter(last_syntactic.w))
            try:
                out.append("  structure : " + labelled_bracket(root))
            except ValueError:            # D13 objects have no labels (D28)
                out.append("  structure : " + _brief(root) + "   (unlabelled: D13)")
        for k, v in d.check().items():
            out.append(f"  {k:<40} {'ok' if v else 'FAILS'}")
        if hasattr(final, "pf"):
            out.append("  PF        : " + pf_string(final.pf))
            out.append("  LF        : " + fmt_lf(final.lf))
            out.append("  CI (D42)  : " + ("converges" if converges_at_ci(d.stages) else "CRASH"))
            out.append("  SM (D43)  : " + ("converges" if converges_at_sm(d.stages) else "CRASH"))
        out.append("")
    if not coda:
        return "\n".join(out)

    # (16)/(17): TransferLF and TransferPF of [VP see Chris] relative to vP.
    d = john_sees_chris()
    i = next(i for i, s in enumerate(d.steps) if s.op == "Cyclic-Transfer")
    vstar_p = next(iter(d.steps[i - 1].stage.w))
    vp = frozenset({T("see", 1), T("Chris", 2)})
    out.append("=" * 74)
    out.append("(16)/(17) TransferLF and TransferPF of [VP see Chris], Phase = v*P")
    out.append("=" * 74)
    out.append(f"  TransferLF(vP, see1)  = {fmt_lf(transfer_lf(vstar_p, T('see', 1)))}")
    out.append(f"  TransferLF(vP, Chris2) = {fmt_lf(transfer_lf(vstar_p, T('Chris', 2)))}")
    out.append(f"  TransferLF(vP, VP)    = {fmt_lf(transfer_lf(vstar_p, vp))}")
    out.append(f"  TransferPF(vP, VP)    = {pf_string(transfer_pf(vstar_p, vp))}")
    out.append("")

    # Theorem 14 (PIC), shown on the v* phase.
    after = d.steps[i].stage
    (root,) = tuple(after.w)
    chris = T("Chris", 2)
    out.append("=" * 74)
    out.append("Theorem 14 (Phase Impenetrability Condition)")
    out.append("=" * 74)
    out.append(f"  before Cyclic-Transfer: Chris2 is contained in v*P -> {contains(vstar_p, chris)}")
    out.append(f"  after  Cyclic-Transfer: Chris2 is contained in v*P -> {contains(root, chris)}")
    out.append("  The complement is now <TransferPF, TransferLF>, which is not a")
    out.append("  syntactic object (D37), so Merge cannot reach into it.")
    out.append("")

    # Section 11: the plug-back-in model against section 12 on (21).
    out.append("=" * 74)
    out.append("Section 11/12: remnant movement under the two models of Transfer")
    out.append("=" * 74)
    for name, fn in (("(19)/(20) one phase", remnant_movement),
                     ("(21) two phases", remnant_across_phases)):
        plug = next(iter(fn().stages[-1].w))
        ntc = fn(cls=NTCDerivation).interfaces
        out.append(f"  {name}")
        out.append(f"    plug-back-in (D36-D38) : {pf_string(plug.pf)}")
        out.append(f"    section 12 (PF, LF maps): {pf_string(ntc.pf)}")
    return "\n".join(out)


if __name__ == "__main__":
    print(report())

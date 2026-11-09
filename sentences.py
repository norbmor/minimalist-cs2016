"""
sentences.py -- seven further constructions, derived with the same axioms.

    python sentences.py          # the same report format as derivations.py

Nothing here is attributed to Collins & Stabler: the paper's examples are in
`derivations.py`.  These are added to show what covering a new
sentence costs, and each one is chosen to exercise a different part of the
system:

    john_seems_to_win             A-movement across a clause boundary that is
                                  not a phase (D35), so no Cyclic-Transfer
                                  intervenes between the two occurrences.
    you_wonder_who_john_will_see  an embedded question: `who` stops at the
                                  embedded phase edge and is pronounced there,
                                  the converse of `successive_cyclic_wh`.
    john_gives_mary_flowers       a head with two selection features: the first
                                  Merge gives the complement (D32) and the
                                  second the specifier (D33).
    mary_praises_john             the plainest transitive clause, as the
                                  baseline for the pair below.
    mary_not_praise_john          a category the axioms have never heard of:
                                  a new `__X` selection feature is all a new
                                  category costs, and D35 does not make the
                                  new head a phase.
    sue_thinks_john_fell          an embedded declarative: two phases, each
                                  cyclically transferred before it is
                                  embedded (D38), and a new word (Sue).
    who_does_sue_think_fell       long-distance subject wh-movement out of the
                                  embedded declarative: `who` must stop at
                                  both phase edges, or it is trapped (T14).

Adding a sentence means adding lexical items (D2) and a sequence of Select /
Merge / Transfer calls (D38).  No definition in `cs2016.py` changes -- with one
exception, noted on `is_strong_phase` below.
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

import derivations as dv
from cs2016 import Derivation, LexicalItem, Lexicon, pho, sem, syn, trig
from derivations import LEX

# ---------------------------------------------------------------------
# The lexicon, extended (D3).  Trigger features are written in discharge
# order; `__X` is satisfied by a complement whose label carries X.
#
# Note what is *not* here: no new category needs a change to `cs2016.py`.
# The one thing that would is `is_strong_phase` (D35), which names Comp and
# v* explicitly -- a new phase head has to be added to PHASE_CATEGORIES.
# ---------------------------------------------------------------------

EXTRA = {
    LexicalItem(sem("MARY"), syn("D"), pho("Mary"), "Mary", "D"),
    LexicalItem(sem("SUE"), syn("D"), pho("Sue"), "Sue", "D"),
    # a silent declarative complementizer with an edge (OP) feature: the
    # escape hatch for wh-movement out of a declarative clause
    LexicalItem(frozenset(), syn("Comp") | trig("__T", "OP"), (), "Comp_edge", "C"),
    LexicalItem(sem("FLOWERS"), syn("D"), pho("flowers"), "flowers", "D"),
    # a raising verb: selects a TP and assigns no external argument
    LexicalItem(sem("SEEM"), syn("V") | trig("__T"), pho("seem"), "seem", "V"),
    # a question-embedding verb: selects a Comp phrase
    LexicalItem(sem("WONDER"), syn("V") | trig("__Comp"), pho("wonder"), "wonder", "V"),
    # two selection features on one head
    LexicalItem(sem("GIVE"), syn("V") | trig("__D", "__D"), pho("give"), "give", "V"),
    # a category no definition in cs2016.py mentions, and a T that selects it
    LexicalItem(sem("PRAISE"), syn("V") | trig("__D"), pho("praise"), "praise", "V"),
    LexicalItem(frozenset(), syn("Neg") | trig("__v*"), pho("not"), "not", "Neg"),
    LexicalItem(frozenset(), syn("T") | trig("__Neg", "EPP"), (), "T_Neg", "T"),
}

LEX2 = Lexicon(set(LEX) | EXTRA)
T = LEX2.token


# ---------------------------------------------------------------------
# 1.  "John seems to win"  --  raising
#
# The infinitival TP is not a strong phase (D35 names only Comp and v*), so
# nothing is transferred between the two occurrences of John and the matrix
# EPP can reach the embedded subject.  Compare (18), where the same movement
# is clause-internal.
# ---------------------------------------------------------------------

def john_seems_to_win(cls=Derivation) -> Derivation:
    john = T("John", 3)
    d = cls(LEX2, [T("win", 1), T("to", 2), john, T("seem", 4),
                   T("T_V", 5), T("Comp", 6)])
    d.select("win", 1)
    d.select_and_merge("to", 2)          # {to2, win1}
    d.select_and_merge("John", 3)        # infinitival TP = {John3, {to2, win1}}
    d.select_and_merge("seem", 4)        # VP = {seem4, TP}
    d.select_and_merge("T_V", 5)         # {T5, VP}
    d.internal_merge(john)               # matrix TP: the EPP raises John3
    d.select_and_merge("Comp", 6)
    d.transfer()
    return d


# ---------------------------------------------------------------------
# 2.  "You wonder who John will see"  --  an embedded question
#
# The embedded clause is built as in `successive_cyclic_wh`: `John` is the
# external argument of `see`, merged in Spec,v*P and raised to Spec,TP; `who`
# moves to the embedded v* edge before that phase's VP is transferred, and
# then to the embedded Spec,CP.  The matrix Comp carries no operator feature,
# so there is nothing to attract it further.  That is its only final occurrence (D40), and TransferPF
# (D41) pronounces it there -- inside the chunk spelled out at the matrix v*
# phase.  `successive_cyclic_wh` is the same embedded clause under a
# matrix Comp_Q, where the wh-phrase must keep going.
# ---------------------------------------------------------------------

def you_wonder_who_john_will_see(cls=Derivation) -> Derivation:
    who, you = T("who", 2), T("you", 8)
    d = cls(LEX2, [T("see", 1), who, T("will", 3), T("John", 4), T("Comp_Q", 5),
                   T("wonder", 6), T("v*", 7), you, T("T", 9), T("Comp", 10),
                   T("v*_edge", 11)])
    d.select("see", 1)
    d.select_and_merge("who", 2)         # VP = {see1, who2}
    d.select_and_merge("v*_edge", 11)
    d.select_and_merge("John", 4)        # embedded v*P: John is the external argument
    d.internal_merge(who)                # embedded v* edge
    d.cyclic_transfer()                  # complement of v*11 -> see
    d.select_and_merge("will", 3)
    d.internal_merge(T("John", 4))       # embedded TP: John raises
    d.select_and_merge("Comp_Q", 5)
    d.internal_merge(who)                # embedded Spec,CP -- the landing site
    d.cyclic_transfer()                  # complement of Comp5 -> John-will-see
    d.select_and_merge("wonder", 6)      # matrix VP = {wonder6, CP}
    d.select_and_merge("v*", 7)
    d.select_and_merge("you", 8)         # matrix v*P -- a strong phase
    d.cyclic_transfer()                  # complement of v*7 -> wonder-who-...
    d.select_and_merge("T", 9)
    d.internal_merge(you)
    d.select_and_merge("Comp", 10)       # declarative: no operator feature
    d.transfer()
    return d


# ---------------------------------------------------------------------
# 3.  "John gives Mary flowers"  --  two selection features on one head
#
# The first Merge of `give` yields its complement (D32) and the second its
# specifier (D33) -- the distinction is structural, by D32/D33, and does not
# depend on which of the two identical __D features D26 is taken to check.
#
# The surface string is `John Mary give flowers`: there is no head movement
# here, so D41b leaves the specifier of VP to the left of the verb.  Getting
# the English order would mean adding head movement, which the paper does not
# formalize and this transcription therefore does not implement.
# ---------------------------------------------------------------------

def john_gives_mary_flowers(cls=Derivation) -> Derivation:
    john = T("John", 5)
    d = cls(LEX2, [T("give", 1), T("flowers", 2), T("Mary", 3), T("v*", 4),
                   john, T("T", 6), T("Comp", 7)])
    d.select("give", 1)
    d.select("flowers", 2)
    d.merge_roots()                      # discharges the first __D: complement
    d.select_and_merge("Mary", 3)        # discharges the second __D: specifier
    d.select_and_merge("v*", 4)
    d.select_and_merge("John", 5)        # v*P -- a strong phase
    d.cyclic_transfer()                  # complement of v*4 -> Mary-give-flowers
    d.select_and_merge("T", 6)
    d.internal_merge(john)
    d.select_and_merge("Comp", 7)
    d.transfer()
    return d


# ---------------------------------------------------------------------
# 4.  A minimal pair: "Mary praises John" / "Mary not praise John"
#
# The affirmative is the plainest transitive clause the system builds: one v*
# phase, Cyclic-Transfer of its complement, the EPP raising the subject.  It
# is here as the baseline the negated version is read against.
#
# The negated version adds `Neg`, a category that appears in no definition in
# cs2016.py.  It costs one selection feature name -- `not` carries __v*, and
# a T variant carries __Neg -- and nothing else: Merge, Transfer and the
# theorems are indifferent to the inventory of categories.  What the engine
# does *not* infer is phasehood: is_strong_phase (D35) names Comp and v*
# explicitly, so NegP is transparent and the v* complement is still what
# Cyclic-Transfer targets.  The two derivations transfer the same chunk.
#
# The function names differ the way the strings do: `Mary praises John` is
# English, `Mary not praise John` is not.  There is no head movement here, so
# no do-support and no inflection, and D41b spells the terminals out in
# Specifier-Head-Complement order.
# ---------------------------------------------------------------------

def mary_praises_john(cls=Derivation) -> Derivation:
    mary = T("Mary", 4)
    d = cls(LEX2, [T("praise", 1), T("John", 2), T("v*", 3), mary,
                   T("T", 5), T("Comp", 6)])
    d.select("praise", 1)
    d.select("John", 2)
    d.merge_roots()                      # VP = {praise1, John2}
    d.select_and_merge("v*", 3)
    d.select_and_merge("Mary", 4)        # v*P -- a strong phase
    d.cyclic_transfer()                  # complement of v*3 -> praise-John
    d.select_and_merge("T", 5)
    d.internal_merge(mary)
    d.select_and_merge("Comp", 6)
    d.transfer()
    return d


def mary_not_praise_john(cls=Derivation) -> Derivation:
    mary = T("Mary", 4)
    d = cls(LEX2, [T("praise", 1), T("John", 2), T("v*", 3), mary,
                   T("not", 5), T("T_Neg", 6), T("Comp", 7)])
    d.select("praise", 1)
    d.select("John", 2)
    d.merge_roots()                      # VP = {praise1, John2}
    d.select_and_merge("v*", 3)
    d.select_and_merge("Mary", 4)        # v*P -- a strong phase
    d.cyclic_transfer()                  # complement of v*3 -> praise-John
    d.select_and_merge("not", 5)         # NegP = {not5, v*P}   -- not a phase
    d.select_and_merge("T_Neg", 6)
    d.internal_merge(mary)
    d.select_and_merge("Comp", 7)
    d.transfer()
    return d


# ---------------------------------------------------------------------
# 5.  "Sue thinks John fell"  --  an embedded declarative
#
# The embedded clause is the paper's (18).  Its CP is a strong phase (D35),
# and D38 forbids embedding a phase whose complement has not been
# transferred, so Cyclic-Transfer spells the embedded TP out (`John fell`)
# before `think` selects the CP.  The matrix v*P is a second phase, handled
# the same way.  Nothing moves out of either phase, so -- unlike (21) -- the
# plug-back-in model and the section 12 Transfer give the same PF.
#
# No head movement or agreement, so the verb surfaces as `think`.
# ---------------------------------------------------------------------

def sue_thinks_john_fell(cls=Derivation) -> Derivation:
    sue = T("Sue", 7)
    d = cls(LEX2, [T("fall", 1), T("John", 2), T("T_V", 3), T("Comp", 4),
                   T("think", 5), T("v*", 6), sue, T("T", 8), T("Comp", 9)])
    # -- embedded clause: (18) John fell --------------------------------
    d.select("fall", 1)
    d.select("John", 2)
    d.merge_roots()                      # VP = {fall1, John2}
    d.select_and_merge("T_V", 3)
    d.internal_merge(T("John", 2))       # embedded TP: John raises
    d.select_and_merge("Comp", 4)        # embedded CP -- a strong phase
    d.cyclic_transfer()                  # complement of Comp4 -> John-fell
    # -- matrix clause --------------------------------------------------
    d.select_and_merge("think", 5)       # VP = {think5, CP}
    d.select_and_merge("v*", 6)
    d.select_and_merge("Sue", 7)         # matrix v*P -- a strong phase
    d.cyclic_transfer()                  # complement of v*6 -> think-John-fell
    d.select_and_merge("T", 8)
    d.internal_merge(sue)                # matrix TP: Sue raises
    d.select_and_merge("Comp", 9)
    d.transfer()
    return d


# ---------------------------------------------------------------------
# 6.  "Who does Sue think fell"  --  long-distance subject wh-movement
#
# `who` starts as the complement of unaccusative `fall`, raises to the
# embedded Spec,TP (the EPP), and then has to leave the embedded clause.  The
# embedded CP and the matrix v*P are strong phases (D35), and each has its
# complement transferred before it is embedded (D38) -- so `who` must first
# move to each edge: the embedded Spec,CP (via Comp_edge) and the matrix v*
# edge (via v*_edge).  It lands in the matrix Spec,CP with five occurrences,
# of which only the highest is final (D40) and pronounced.
#
# With `escape_the_embedded_CP=False` the embedded clause gets the plain
# Comp, which has no edge feature: `who` stays inside the TP that
# Cyclic-Transfer replaces, and the next movement is refused (T14).
#
# No head movement, so no T-to-C and no do-support: PF is `who Sue think fell`.
# ---------------------------------------------------------------------

def who_does_sue_think_fell(cls=Derivation,
                            escape_the_embedded_CP: bool = True) -> Derivation:
    who, sue = T("who", 2), T("Sue", 7)
    comp = "Comp_edge" if escape_the_embedded_CP else "Comp"
    d = cls(LEX2, [T("fall", 1), who, T("T_V", 3), T(comp, 4), T("think", 5),
                   T("v*_edge", 6), sue, T("T", 8), T("Comp_Q", 9)])
    # -- embedded clause: who fell ---------------------------------------
    d.select("fall", 1)
    d.select("who", 2)
    d.merge_roots()                      # VP = {fall1, who2}
    d.select_and_merge("T_V", 3)
    d.internal_merge(who)                # embedded Spec,TP (EPP)
    d.select_and_merge(comp, 4)          # embedded CP -- a strong phase
    if escape_the_embedded_CP:
        d.internal_merge(who)            # embedded Spec,CP            edge 1
    d.cyclic_transfer()                  # complement of C4 -> fell
    # -- matrix clause ---------------------------------------------------
    d.select_and_merge("think", 5)       # VP = {think5, CP}
    d.select_and_merge("v*_edge", 6)
    d.select_and_merge("Sue", 7)         # matrix v*P -- a strong phase
    d.internal_merge(who)                # matrix v* edge              edge 2
    d.cyclic_transfer()                  # complement of v*6 -> think fell
    d.select_and_merge("T", 8)
    d.internal_merge(sue)                # matrix Spec,TP
    d.select_and_merge("Comp_Q", 9)
    d.internal_merge(who)                # matrix Spec,CP              landing
    d.transfer()
    return d


ALL = {
    "John seems to win (raising over a non-phase)": john_seems_to_win,
    "You wonder who John will see (embedded question)": you_wonder_who_john_will_see,
    "John gives Mary flowers (two selection features)": john_gives_mary_flowers,
    "Mary praises John (the affirmative baseline)": mary_praises_john,
    "Mary not praise John (a category the axioms do not know)": mary_not_praise_john,
    "Sue thinks John fell (embedded declarative)": sue_thinks_john_fell,
    "Who does Sue think fell (long-distance subject wh)": who_does_sue_think_fell,
}


if __name__ == "__main__":
    print(dv.report(ALL, coda=False))

"""
test_sentences.py -- checks on the seven constructions in `sentences.py`.

`test_cs2016.py` has one check per definition, theorem or extension; this file
has one per *sentence*, asserting the property each was added to exhibit.
Run with pytest, or directly:  python test_sentences.py
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

import sentences as sn
from functools import partial

from cs2016 import (
    TRANSFER_NTC_KEY, Derivation, NTCDerivation, Transferred, complement_of,
    converges, is_nonfinal_occurrence, is_strong_phase, label, positions,
    specifier_of,
)
from sentences import LEX2, T


def _pf(x) -> str:
    return " ".join(f.name for f in x.pf) or "(silence)"


def _final(d) -> Transferred:
    (x,) = tuple(d.stages[-1].w)
    return x


def _chunk_at(d: Derivation, nth: int) -> Transferred:
    """The object Cyclic-Transfer produced at the `nth` such step (0-based)."""
    i = [j for j, s in enumerate(d.steps) if s.op == "Cyclic-Transfer"][nth]
    (root,) = tuple(d.steps[i].stage.w)
    found = []

    def walk(X):
        if isinstance(X, Transferred):
            found.append(X)
        elif isinstance(X, frozenset):
            for m in X:
                walk(m)
    walk(root)
    assert len(found) == 1, f"expected one transferred chunk, got {len(found)}"
    return found[0]


# =====================================================================
# 1.  Raising
# =====================================================================

def test_raising_crosses_no_phase_boundary():
    """Nothing is transferred between the two occurrences of John."""
    d = sn.john_seems_to_win()
    assert not [s for s in d.steps if s.op == "Cyclic-Transfer"]
    n = sn.john_seems_to_win(cls=NTCDerivation)
    infinitival = next(m for m in n.root if isinstance(m, frozenset))
    assert not is_strong_phase(infinitival)      # D35 names only Comp and v*


def test_raising_leaves_two_occurrences_and_pronounces_the_higher():
    d = sn.john_seems_to_win()
    assert _pf(_final(d)) == "John seem to win"
    n = sn.john_seems_to_win(cls=NTCDerivation)
    ps = positions(T("John", 3), n.root)
    assert len(ps) == 2                                        # D16/D17
    assert sum(1 for p in ps if not is_nonfinal_occurrence(p, n.root)) == 1   # D40


# =====================================================================
# 2.  Embedded question
# =====================================================================

def test_embedded_question_pronounces_who_at_the_embedded_edge():
    d = sn.you_wonder_who_john_will_see()
    assert _pf(_final(d)) == "you wonder who John will see"
    # the embedded VP, at the embedded v* phase (who has moved to its edge)
    assert _pf(_chunk_at(d, 0)) == "see"
    # the embedded TP, spelled out at the embedded Comp phase
    assert _pf(_chunk_at(d, 1)) == "John will see"
    # who is realized inside the chunk transferred at the matrix v* phase,
    # i.e. at the embedded edge and not at the matrix one
    assert _pf(_chunk_at(d, 2)) == "wonder who John will see"


def test_who_stops_at_the_embedded_edge_with_no_matrix_operator():
    n = sn.you_wonder_who_john_will_see(cls=NTCDerivation)
    ps = positions(T("who", 2), n.root)
    assert len(ps) == 3            # in situ, embedded v* edge, embedded Spec,CP
    (final,) = [p for p in ps if not is_nonfinal_occurrence(p, n.root)]
    # the matrix CP is not the final occurrence's mother: who is embedded
    assert len(final) > 2


def test_the_embedded_question_needs_the_occurrence_reading_of_section_12():
    """Section 12: `who` moves on from the embedded v* edge after that
    phase's VP is transferred.  Under the occurrence reading the edge copy is
    accessible and both models of Transfer agree; under the object reading
    `who` is contained in the transferred VP and cannot move to Spec,CP."""
    want = _pf(_final(sn.you_wonder_who_john_will_see()))
    assert _pf(sn.you_wonder_who_john_will_see(cls=NTCDerivation).interfaces) == want
    try:
        sn.you_wonder_who_john_will_see(cls=partial(NTCDerivation, reading="object"))
    except ValueError as e:
        assert "accessible" in str(e)
    else:
        raise AssertionError("expected the object reading to block who")


# =====================================================================
# 3.  Two selection features on one head
# =====================================================================

def test_two_selection_features_give_a_complement_then_a_specifier():
    """D32/D33: the first Merge of a head gives its complement, the next its
    specifier -- whichever of the two __D features D26 is taken to check."""
    n = sn.john_gives_mary_flowers(cls=NTCDerivation)
    give = T("give", 1)
    (p,) = positions(give, n.root)
    v_bar, vp = p[-2], p[-3]
    assert complement_of(give, v_bar) == T("flowers", 2)       # D32
    assert specifier_of(v_bar, vp) == T("Mary", 3)             # D33


def test_the_ditransitive_surfaces_without_head_movement():
    """D41b puts the specifier of VP before the verb; nothing reorders it."""
    assert _pf(_final(sn.john_gives_mary_flowers())) == "John Mary give flowers"


# =====================================================================
# 4.  A category the axioms do not know
# =====================================================================

def test_the_affirmative_baseline():
    assert _pf(_final(sn.mary_praises_john())) == "Mary praise John"


def test_negation_adds_one_word_and_changes_nothing_else():
    """NegP is transparent: the same chunk is transferred at the v* phase."""
    aff, neg = sn.mary_praises_john(), sn.mary_not_praise_john()
    assert _pf(_chunk_at(aff, 0)) == _pf(_chunk_at(neg, 0)) == "praise John"
    a, n = _pf(_final(aff)).split(), _pf(_final(neg)).split()
    assert n == a[:1] + ["not"] + a[1:]


def test_a_new_category_costs_one_selection_feature_and_nothing_else():
    d = sn.mary_not_praise_john()
    assert _pf(_final(d)) == "Mary not praise John"
    checks = d.check()
    assert all(v for k, v in checks.items() if k != TRANSFER_NTC_KEY)


def test_the_new_head_does_not_become_a_phase():
    """D35 names Comp and v* explicitly: NegP is transparent."""
    n = sn.mary_not_praise_john(cls=NTCDerivation)
    (p,) = positions(T("not", 5), n.root)
    negp = p[-2]
    assert label(negp) == T("not", 5)          # D28: Neg projects
    assert not is_strong_phase(negp)           # D35
    # and so Cyclic-Transfer still targeted the complement of v*, not of Neg
    assert _pf(_chunk_at(sn.mary_not_praise_john(), 0)) == "praise John"


# =====================================================================
# 5.  An embedded declarative
# =====================================================================

def test_embedded_declarative_transfers_each_phase_before_embedding_it():
    """D38: the embedded CP's complement is spelled out before `think`
    selects it, and the matrix v*P's before T does."""
    d = sn.sue_thinks_john_fell()
    assert _pf(_final(d)) == "Sue think John fell"
    assert _pf(_chunk_at(d, 0)) == "John fell"            # the paper's (18)
    assert _pf(_chunk_at(d, 1)) == "think John fell"
    assert converges(d.stages)


def test_embedded_declarative_is_the_same_under_both_models_of_transfer():
    """Nothing moves out of a phase, so section 12 changes nothing."""
    d = sn.sue_thinks_john_fell()
    n = sn.sue_thinks_john_fell(cls=NTCDerivation)
    assert _pf(n.interfaces) == _pf(_final(d))
    assert n.interfaces.lf == _final(d).lf


# =====================================================================
# 6.  Long-distance subject wh-movement
# =====================================================================

def test_long_distance_subject_wh():
    d = sn.who_does_sue_think_fell()
    assert _pf(_final(d)) == "who Sue think fell"
    assert _pf(_chunk_at(d, 0)) == "fell"              # who has left the TP
    assert _pf(_chunk_at(d, 1)) == "think fell"        # ... and the VP
    assert converges(d.stages)


def test_who_has_five_occurrences_and_one_is_pronounced():
    """In situ, embedded Spec,TP, embedded Spec,CP, v* edge, matrix Spec,CP."""
    n = sn.who_does_sue_think_fell(cls=NTCDerivation)
    ps = positions(T("who", 2), n.root)
    assert len(ps) == 5
    (final,) = [p for p in ps if not is_nonfinal_occurrence(p, n.root)]
    assert len(final) == 2                             # daughter of the root CP


def test_who_is_trapped_without_the_embedded_edge():
    """With plain Comp, who is inside the transferred TP (T14)."""
    msg = ""
    try:
        sn.who_does_sue_think_fell(escape_the_embedded_CP=False)
    except ValueError as e:
        msg = str(e)
    assert "PIC" in msg


def test_long_distance_wh_needs_the_occurrence_reading_of_section_12():
    """Same PF under plug-back-in and section 12 (occurrence reading); the
    object reading makes the edge copy of who inaccessible."""
    want = _pf(_final(sn.who_does_sue_think_fell()))
    assert _pf(sn.who_does_sue_think_fell(cls=NTCDerivation).interfaces) == want
    try:
        sn.who_does_sue_think_fell(cls=partial(NTCDerivation, reading="object"))
    except ValueError as e:
        assert "accessible" in str(e)
    else:
        raise AssertionError("expected the object reading to block who")


# =====================================================================
# All seven
# =====================================================================

def test_every_sentence_satisfies_the_general_theorems():
    for name, fn in sn.ALL.items():
        checks = fn().check()
        failed = [k for k, v in checks.items() if not v and k != TRANSFER_NTC_KEY]
        assert not failed, f"{name}: {failed}"


def test_every_sentence_converges():
    for name, fn in sn.ALL.items():
        assert converges(fn().stages), name


def test_the_lexicon_extension_leaves_the_paper_derivations_alone():
    import derivations as dv
    assert set(dv.LEX) < set(LEX2)
    for fn in dv.ALL.values():
        assert fn().check()["D14/D38 derivation"]


def test_every_registered_derivation_draws():
    """figures.derivation_figure handles everything in the registry.

    Skipped when matplotlib is not installed: the rest of this suite, and all
    of test_cs2016.py, is standard library only.
    """
    try:
        import figures
    except ImportError:                                  # pragma: no cover
        return
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        for name, (_title, fn) in figures.REGISTRY.items():
            out = figures.derivation_figure(fn, os.path.join(tmp, name + ".png"))
            assert os.path.getsize(out) > 0, name
    assert set(sn.ALL) <= {t for t, _ in figures.REGISTRY.values()}


if __name__ == "__main__":
    import traceback
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failed = 0
    for t in tests:
        try:
            t()
            print(f"PASS  {t.__name__}")
        except Exception:
            failed += 1
            print(f"FAIL  {t.__name__}")
            traceback.print_exc()
    print(f"\n{len(tests) - failed}/{len(tests)} passed")

"""
test_cs2016.py -- the definitions and theorems of Collins & Stabler (2016),
each as an executable check.  Run with pytest, or directly:  python test_cs2016.py
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


import cs2016 as cs
from cs2016 import (
    ChainSO, Derivation, NTCDerivation, Stage, TRANSFER_NTC_KEY, Transferred,
    all_paths, c_commands, asymmetrically_c_commands, chain_locality_ok,
    chain_merge, chain_positions, complement_of, contains, converges,
    converges_at_ci, converges_at_sm, derived_object, immediately_contains,
    is_accessible, is_binary_branching, is_chain_derivation, is_derivation,
    is_final, is_intermediate_projection, is_maximal_projection,
    is_minimal_projection, is_nonfinal_occurrence, is_strong_phase,
    is_syntactic_object, label, merge, occ_c_commands, pf_string, positions,
    satisfies_extension, satisfies_inclusiveness, satisfies_ntc, select,
    specifier_of, theorem1_holds, theorem2_holds, theorem3_holds,
    theorem4_report, transfer, transfer_lf, transfer_pf, triggered_merge,
    triggers, unique_root_occurrences,
)
import derivations as dv
from derivations import LEX

tok = LEX.token


def _pf(x) -> str:
    return pf_string(x.pf)


def _final(d):
    (x,) = tuple(d.stages[-1].w)
    return x


def _raises(fn, *args) -> str:
    try:
        fn(*args)
    except (ValueError, AssertionError) as e:
        return str(e)
    raise AssertionError(f"{fn.__name__} should have been undefined")


# ================================================================ section 2
# ---------------------------------------------------------------- D2, D5, D6
def test_lexical_item_is_a_triple():
    see = LEX.by_name("see")
    assert all(f.kind == cs.SEM for f in see.sem)
    assert all(f.kind == cs.SYN for f in see.syn)
    assert all(f.kind == cs.PHON for f in see.phon)


def test_tokens_of_one_item_are_distinct():
    assert tok("John", 1) != tok("John", 2)
    assert tok("John", 1).li is tok("John", 2).li


# ---------------------------------------------------------------- D7 / D37
def test_syntactic_objects():
    j, c = tok("John", 1), tok("Chris", 2)
    assert is_syntactic_object(j)
    assert is_syntactic_object(frozenset({j, c}))
    assert not is_syntactic_object(Transferred((), None))           # D37: not an SO
    assert is_syntactic_object(frozenset({j, Transferred((), None)}))  # D37ii


# ---------------------------------------------------------------- D8, D9
def test_containment():
    j, c = tok("John", 1), tok("Chris", 2)
    vp = frozenset({j, c})
    tp = frozenset({vp, tok("T", 3)})
    assert immediately_contains(vp, j) and not immediately_contains(tp, j)
    assert contains(tp, j) and contains(tp, vp) and not contains(tp, tp)


# ================================================================ section 3
# ---------------------------------------------------------------- D12
def test_select_only_from_the_lexical_array():
    s = Stage(frozenset({tok("John", 1)}), frozenset())
    assert select(tok("John", 1), s) == Stage(frozenset(), frozenset({tok("John", 1)}))
    assert "D12" in _raises(select, tok("Chris", 2), s)


# ---------------------------------------------------------------- D13
def test_merge_requires_distinctness():
    j = tok("John", 1)
    assert merge(j, tok("Chris", 2)) == frozenset({j, tok("Chris", 2)})
    assert "D13" in _raises(merge, j, j)


# ---------------------------------------------------------------- D14, D15, (6)-(8)
def test_example_6_external_merge():
    """(4)/(6)/(8): two tokens of John, six stages."""
    d = dv.external_merge_6()
    assert len(d.stages) == 6
    A = derived_object(d.stages, LEX, merge)
    assert A == frozenset({tok("John", 2), frozenset({tok("see", 1), tok("John", 1)})})


def test_example_7_internal_merge():
    """(2)/(7): one token of John, two occurrences, five stages."""
    d = dv.internal_merge_7()
    assert len(d.stages) == 5
    A = derived_object(d.stages, LEX, merge)
    assert A == frozenset({tok("John", 1), frozenset({tok("see", 1), tok("John", 1)})})
    assert len(positions(tok("John", 1), A)) == 2


def test_d14_is_a_derivation_d15_adds_completion():
    """D14 no longer requires LA_n = {} or one root; that is D15."""
    d = dv.john_fell()
    partial = d.stages[:4]
    assert is_derivation(partial, LEX)
    assert derived_object(partial, LEX) is None
    assert derived_object(dv.vp_see_chris().stages, LEX) is not None


def test_merge_must_be_at_the_root():
    """D14(a): A must be a root; sideward Merge is excluded by D14(b)."""
    d = dv.vp_see_chris()
    d.select  # a single root {see1, Chris2}
    s = d.stage
    msg = _raises(cs.apply_merge, s, tok("see", 1), tok("Chris", 2))
    assert "D11, D14a" in msg


# ================================================================ section 4
# ---------------------------------------------------------------- D16-D18, T1
def test_two_occurrences_of_a_moved_object():
    d = dv.john_fell()
    root = next(iter(d.steps[-2].stage.w))                 # before Transfer
    ps = positions(tok("John", 2), root)
    assert len(ps) == 2
    assert len({len(p) for p in ps}) == 2                  # one higher, one lower


# ---------------------------------------------------------------- D19-D22, T1-T3
def test_occurrence_relations_and_theorems_1_to_3():
    d = dv.john_fell()
    root = next(iter(d.steps[-2].stage.w))
    hi, lo = sorted(positions(tok("John", 2), root), key=len)
    assert occ_c_commands(hi, lo) and not occ_c_commands(lo, hi)      # D22
    assert c_commands(tok("John", 2), tok("John", 2), root)           # D21
    assert asymmetrically_c_commands(tok("John", 2), tok("T_V", 3), root)
    # D21 is object-level: John2 and fall1 are sisters in VP, so even the
    # raised John2 does not *asymmetrically* c-command fall1.
    assert not asymmetrically_c_commands(tok("John", 2), tok("fall", 1), root)
    for fn in (dv.john_fell, dv.remnant_movement, dv.successive_cyclic_wh):
        r = next(iter(fn(cls=NTCDerivation).stage.w))
        assert theorem1_holds(r) and theorem2_holds(r) and theorem3_holds(r)


# ================================================================ section 5
def test_chain_based_examples_7_and_8():
    """(7') and (8'): Chain-based derivations of (2) and (4)."""
    john, see = ChainSO(LEX.by_name("John")), ChainSO(LEX.by_name("see"))
    js = chain_merge(john, see)
    (path,) = [p for p in chain_positions(john, js)]
    seq7 = [john, see, js, chain_merge(js, john, path)]
    seq8 = [john, see, js, chain_merge(john, js)]
    items = [LEX.by_name("John"), LEX.by_name("see")]
    assert is_chain_derivation(seq7, items) and is_chain_derivation(seq8, items)
    assert seq7[-1] != seq8[-1]                            # the path tells them apart
    # Chain-based Merge cannot merge a lexical item with itself
    assert "D13'" in _raises(chain_merge, john, john)


def test_locality_condition_as_printed_blocks_every_internal_merge():
    """D14'(c) quantifies over every i < k, which includes B's mother: read
    literally it would rule out (7').  We read it as i < k-1."""
    john, see = ChainSO(LEX.by_name("John")), ChainSO(LEX.by_name("see"))
    js = chain_merge(john, see)
    (path,) = chain_positions(john, js)
    literal = all(john not in node.s for node in path[:-1] if isinstance(node.s, frozenset))
    assert not literal
    assert chain_locality_ok(john, path)


def test_theorem_4_holds_up_to_size_2():
    items = [LEX.by_name("John"), LEX.by_name("see")]
    for loc in (True, False):
        assert theorem4_report(items, 2, loc)["bijection"]


def test_theorem_4_fails_at_size_3_with_locality():
    """With D14'(c), the token-based system can move a lower token across a
    higher token of the same lexical item; the Chain-based one cannot."""
    items = [LEX.by_name("John"), LEX.by_name("see")]
    r = theorem4_report(items, 3, locality=True)
    no_image = [X for X, cs_ in r["token objects without a unique chain image"] if not cs_]
    assert no_image and not r["bijection"]
    # ... and that token object really is derivable (D15) with D13 Merge
    d = Derivation(LEX, [tok("John", 1), tok("see", 2), tok("see", 3)], merge_rule=merge)
    d.select("John", 1).select("see", 2).merge_roots()
    d.select("see", 3).merge_roots()
    d.internal_merge(tok("see", 2))
    A = derived_object(d.stages, LEX, merge)
    assert cs.renumbering_class(A) in {cs.renumbering_class(X) for X in no_image}


def test_theorem_4_fails_at_size_3_without_locality():
    """Without D14'(c), the Chain-based system records *which* occurrence was
    re-merged, and the token-based one does not."""
    items = [LEX.by_name("John"), LEX.by_name("see")]
    r = theorem4_report(items, 3, locality=False)
    assert any(len(cs_) > 1 for _, cs_ in r["token objects without a unique chain image"])


def test_theorem_4_remnant_configurations_have_two_chain_images():
    items = [LEX.by_name("John"), LEX.by_name("see")]
    r = theorem4_report(items, 5, locality=True)
    assert any(len(cs_) == 2 for _, cs_ in r["token objects without a unique chain image"])


# ================================================================ section 6
def test_binary_branching():                                          # D24, T5
    for fn in dv.ALL.values():
        for x in fn().stages[-1].w:
            assert is_binary_branching(x)


def test_uniqueness_of_root_occurrences():                            # T6
    j, c = tok("John", 1), tok("Chris", 2)
    a = frozenset({j, c})
    assert unique_root_occurrences(frozenset({a}))
    assert not unique_root_occurrences(frozenset({a, j}))   # (10): underivable
    for fn in dv.ALL.values():
        for s in fn().stages:
            assert unique_root_occurrences(s.w)


def test_two_occurrences_iff_internal_merge():                        # T7
    no_im = dv.vp_see_chris()
    root = next(iter(no_im.stages[-1].w))
    assert all(len(positions(o, root)) == 1 for o in [root] + cs._all_contained(root))
    for fn in dv.ALL.values():
        assert fn().check()["T7 two occurrences iff internal Merge"]


def test_ntc_extension_inclusiveness_over_the_syntax():              # T8-T10
    for fn in dv.ALL.values():
        d = fn()
        st = d.stages
        for i, step in enumerate(d.steps):
            if i == 0 or step.op not in ("Merge", "Select"):
                continue
            assert satisfies_ntc(st[i - 1], st[i])
            if step.op == "Merge":
                assert satisfies_extension(st[i - 1], st[i])
        assert satisfies_inclusiveness(st)


def test_trace_theory_would_violate_the_ntc():
    """Section 6: replacing the lower copy by a trace is not NTC-compliant."""
    see, john = tok("see", 1), tok("John", 1)
    A = frozenset({see, john})
    traced = frozenset({frozenset({see, tok("Chris", 9)}), john})  # stand-in for t
    assert not satisfies_ntc(Stage(frozenset(), frozenset({A})),
                             Stage(frozenset(), frozenset({traced})))


def test_cyclic_transfer_violates_the_ntc():
    """Section 8: the plug-back-in model is not NTC-compliant."""
    for fn in (dv.john_fell, dv.john_sees_chris, dv.remnant_movement):
        assert not fn().check()[TRANSFER_NTC_KEY]


# ================================================================ section 7
def test_triggered_merge_is_asymmetric():                             # D27, T12
    see, chris = tok("see", 1), tok("Chris", 2)
    assert triggered_merge(see, chris) == frozenset({see, chris})
    assert "D27" in _raises(triggered_merge, chris, see)


def test_example_15_two_trigger_features():                           # D26, (15)
    d = dv.two_trigger_features_15()
    A = derived_object(d.stages, LEX)
    see = tok("see_2TF", 2)
    assert len(triggers(see)) == 2
    assert len(triggers(frozenset({see, tok("John", 1)}))) == 1       # after (15c)
    assert triggers(A) == ()                                          # after (15d)
    assert A == frozenset({tok("John", 1), frozenset({see, tok("John", 1)})})


def test_which_trigger_is_checked_does_not_affect_derivability():
    """D26 leaves the choice open; under D27 only the count matters."""
    import extensions as ext
    la = frozenset({tok("see", 1), tok("Chris", 2), tok("T_V", 3), tok("Comp", 4)})
    n1, f1, _ = ext.explore(la, triggered_merge)
    with ext.unordered_triggers():
        n2, f2, _ = ext.explore(la, triggered_merge)
    assert (n1, f1) == (n2, f2)


def test_labels_and_projections():                                    # D28-D33, T13
    see, chris, vstar = tok("see", 1), tok("Chris", 2), tok("v*", 3)
    vp = triggered_merge(see, chris)
    assert label(vp) == see
    vbar = triggered_merge(vstar, vp)
    assert label(vbar) == vstar
    vp_phase = triggered_merge(vbar, tok("John", 4))
    assert label(vp_phase) == vstar                       # T13
    assert complement_of(see, vp) == chris                # D32
    assert specifier_of(vbar, vp_phase) == tok("John", 4)  # D33
    assert is_minimal_projection(see)                     # D30
    assert is_maximal_projection(vp_phase, vp_phase)      # D29
    assert is_intermediate_projection(vbar, vp_phase)     # D31
    assert not is_maximal_projection(vbar, vp_phase)


# ================================================================ section 8
def test_strong_phases_are_maximal_projections():                     # D35
    see, chris, vstar = tok("see", 1), tok("Chris", 2), tok("v*", 3)
    vp = triggered_merge(see, chris)
    vbar = triggered_merge(vstar, vp)
    vp_phase = triggered_merge(vbar, tok("John", 4))
    assert not is_strong_phase(vp)
    assert is_strong_phase(vp_phase)
    assert not is_strong_phase(vbar, root=vp_phase)       # v*' is not maximal
    d = dv.john_fell()
    assert is_strong_phase(next(iter(d.steps[-2].stage.w)))   # CP


def test_transfer_is_relativized_to_a_phase_and_needs_no_triggers():  # D34
    see = tok("see", 1)
    assert "D34" in _raises(transfer, see, see)


def test_d38_forces_transfer_of_an_embedded_phase():
    """D38: no Transfer of a phase that contains a strong phase whose
    complement has not been transferred."""
    d = dv.Derivation(LEX, [tok("see", 1), tok("Chris", 2), tok("v*", 3), tok("John", 4),
                            tok("T", 5), tok("Comp", 6)])
    d.select("see", 1).select("Chris", 2).merge_roots()
    d.select_and_merge("v*", 3)
    d.select_and_merge("John", 4)
    d.select_and_merge("T", 5)                # skip Cyclic-Transfer at v*P
    d.internal_merge(tok("John", 4))
    d.select_and_merge("Comp", 6)
    assert "D38" in _raises(d.transfer)
    assert "D38" in _raises(d.cyclic_transfer)


def test_pic():                                                       # T14
    d = dv.john_sees_chris()
    i = next(i for i, s in enumerate(d.steps) if s.op == "Cyclic-Transfer")
    before = next(iter(d.steps[i - 1].stage.w))
    after = next(iter(d.steps[i].stage.w))
    chris = tok("Chris", 2)
    assert contains(before, chris)
    assert not contains(after, chris)
    assert cs.pic_blocks(after, chris)


# ================================================================ section 9
def test_example_16_transfer_lf():                                    # D39
    d = dv.john_sees_chris()
    i = next(i for i, s in enumerate(d.steps) if s.op == "Cyclic-Transfer")
    vstar_p = next(iter(d.steps[i - 1].stage.w))
    lf = transfer_lf(vstar_p, tok("Chris", 2))
    assert lf.k == 2 and {f.name for f in lf.sem} == {"CHRIS"}
    vp = frozenset({tok("see", 1), tok("Chris", 2)})
    assert cs.fmt_lf(transfer_lf(vstar_p, vp)) == "{CHRIS_2, SEE_1}"


# ================================================================ section 10
def test_example_17_transfer_pf():                                    # D41b
    d = dv.john_sees_chris()
    i = next(i for i, s in enumerate(d.steps) if s.op == "Cyclic-Transfer")
    vstar_p = next(iter(d.steps[i - 1].stage.w))
    vp = frozenset({tok("see", 1), tok("Chris", 2)})
    assert pf_string(transfer_pf(vstar_p, vp)) == "see Chris"


def test_example_18_finality():                                       # D40, D41c
    d = dv.john_fell()
    cp = next(iter(d.steps[-2].stage.w))
    vp = frozenset({tok("fall", 1), tok("John", 2)})
    assert not is_final(tok("John", 2), vp, cp)          # LI2 is non-final
    assert pf_string(transfer_pf(cp, vp)) == "fell"       # TransferPF(CP, SO) = /fall/
    assert _pf(_final(d)) == "John fell"


def test_specifier_head_complement_order():                           # D41b
    order = _pf(_final(dv.john_sees_chris())).split()
    assert order.index("John") < order.index("see") < order.index("Chris")


# ================================================================ section 11
def test_example_20_remnant_movement_in_one_phase():
    """(20d): John in {John, {to, win}} is non-final in *both* occurrences of
    the moved phrase, because TP contains {John, {to, win}} and has John as a
    member (D40).  One Transfer at (20d) gives the right string."""
    d = dv.remnant_movement()
    cp = next(iter(d.steps[-2].stage.w))
    john = tok("John", 1)
    low = frozenset({john, frozenset({tok("to", 3), tok("win", 2)})})
    assert not is_final(john, low, cp)
    paths = [p for p in positions(john, cp) if p[-2] == low]
    assert len(paths) == 2 and all(is_nonfinal_occurrence(p, cp) for p in paths)
    assert _pf(_final(d)) == "how likely to win John is"


def test_transfer_at_20c_would_block_the_remnant():
    """'If Transfer applied at step (20c), nothing would be able to undergo
    internal Merge out of TP.'"""
    d = dv.Derivation(LEX, [tok("win", 2), tok("to", 3), tok("John", 1), tok("likely", 4),
                            tok("how", 5), tok("is", 6), tok("Comp_Q", 7)])
    d.select("win", 2)
    for name, k in (("to", 3), ("John", 1), ("likely", 4), ("how", 5)):
        d.select_and_merge(name, k)
    degp = d.root
    d.select_and_merge("is", 6)
    d.internal_merge(tok("John", 1))
    d.select_and_merge("Comp_Q", 7)                       # (20c)
    d.cyclic_transfer()
    assert not contains(d.root, degp)
    assert "PIC" in _raises(d.internal_merge, degp)


def test_example_21_plug_back_in_pronounces_john_twice():
    """(21): after the embedded TP has been replaced by its interface pair,
    nothing at the matrix level makes John in the moved DegP non-final."""
    pf = _pf(_final(dv.remnant_across_phases()))
    assert pf == "how likely John to win you think that John is"
    assert pf.split().count("John") == 2


def test_the_same_failure_inside_one_phase():
    """D38 also licenses Cyclic-Transfer at (20d) followed by Transfer; the
    plug-back-in model then mispronounces even the one-phase example."""
    d = dv.Derivation(LEX, [tok("win", 2), tok("to", 3), tok("John", 1), tok("likely", 4),
                            tok("how", 5), tok("is", 6), tok("Comp_Q", 7)])
    d.select("win", 2)
    for name, k in (("to", 3), ("John", 1), ("likely", 4), ("how", 5), ("is", 6)):
        d.select_and_merge(name, k)
    d.internal_merge(tok("John", 1))
    d.select_and_merge("Comp_Q", 7)
    d.internal_merge(dv._degp(d.root))                    # (20d)
    d.cyclic_transfer()
    d.transfer()
    assert is_derivation(d.stages, LEX)
    assert _pf(_final(d)) == "how likely John to win John is"


# ================================================================ section 12
def test_section_12_respects_the_ntc_and_needs_only_d7():
    for fn in (dv.john_fell, dv.john_sees_chris, dv.remnant_movement,
               dv.remnant_across_phases, dv.successive_cyclic_wh):
        d = fn(cls=NTCDerivation)
        assert d.check()[TRANSFER_NTC_KEY]
        assert all(not isinstance(x, Transferred) for x in all_paths(d.root))  # D7 suffices


def test_section_12_still_gives_the_pic():
    d = dv.john_sees_chris(cls=NTCDerivation)
    chris = tok("Chris", 2)
    assert contains(d.root, chris)                         # structure unmodified
    assert not any(is_accessible(p, d.ntc.domain()) for p in positions(chris, d.root))
    assert "T14" in _raises(d.merge, d.root, chris)


def test_section_12_solves_example_21():
    a = dv.remnant_across_phases(cls=NTCDerivation).interfaces
    assert _pf(a) == "how likely to win you think that John is"


def test_the_two_models_agree_where_nothing_straddles_a_phase():
    for name in ("john_fell", "john_sees_chris", "remnant_movement",
                 "successive_cyclic_wh", "crashing"):
        a = _final(getattr(dv, name)())
        b = getattr(dv, name)(cls=NTCDerivation).interfaces
        assert _pf(a) == _pf(b), name
        assert a.lf == b.lf, name


def test_object_reading_of_accessibility_blocks_successive_cyclicity():
    """'W minus those already transferred', read as 'minus every object
    contained in a transferred object', makes `who` inaccessible once the
    embedded TP is transferred, although it also sits at the CP edge."""
    from functools import partial
    msg = _raises(partial(dv.successive_cyclic_wh,
                          cls=partial(NTCDerivation, reading="object")))
    assert "accessible" in msg
    assert dv.successive_cyclic_wh(cls=NTCDerivation).interfaces is not None


def test_section_12_stages_do_not_record_the_interfaces():
    """D10 stages are <LA, W>; section 12 puts Transfer's effect elsewhere, so
    a Transfer step repeats the stage and D38 rejects the sequence."""
    d = dv.john_fell(cls=NTCDerivation)
    checks = d.check()
    assert not checks["D14/D38 derivation"]
    assert checks["D14 derivation (Select/Merge stages only)"]
    assert not converges(d.stages)                         # D42-D44 do not apply


# ================================================================ section 13
def test_convergence_and_crash():                                     # D42-D44
    good = dv.john_sees_chris()
    assert converges_at_ci(good.stages) and converges_at_sm(good.stages)
    assert converges(good.stages)
    bad = dv.crashing()
    assert not converges_at_ci(bad.stages)     # uninterpretable SEM feature
    assert converges_at_sm(bad.stages)
    assert not converges(bad.stages)


# =====================================================================
# Extension 1: selectional Merge  (extensions.py)
# =====================================================================

import extensions as ext


def _small_la():
    return frozenset({tok("see", 1), tok("Chris", 2), tok("T_V", 3), tok("Comp", 4)})


def test_selection_is_a_filter_on_derivability():
    la = _small_la()
    n_free, finals_free, _ = ext.explore(la, cs.triggered_merge)
    n_sel, finals_sel, _ = ext.explore(la, ext.selectional_merge)
    assert finals_sel < finals_free            # proper subset
    assert 0 < n_sel < n_free


def test_selection_leaves_the_general_theorems_intact():
    la = _small_la()
    for rule in (cs.triggered_merge, ext.selectional_merge, ext.make_selectional_merge("D")):
        assert all(ext.theorems_hold_everywhere(la, rule).values())
    with ext.unordered_triggers():
        assert all(ext.theorems_hold_everywhere(
            la, ext.make_selectional_merge(ordered=False)).values())


def test_epp_without_a_categorial_requirement_lets_phrases_raise():
    la = _small_la()
    _, with_sel, _ = ext.explore(la, ext.selectional_merge)
    _, with_epp_d, _ = ext.explore(la, ext.make_selectional_merge("D"))
    assert with_epp_d < with_sel


def test_unranked_triggers_admit_a_dp_complement_of_t():
    """Section 7's worry: with unordered trigger features, what stops
    [TP vP [T' T DP]]?  With an externally merged DP, nothing does."""
    la = frozenset({tok("see", 1), tok("Chris", 2), tok("v*", 3), tok("John", 4),
                    tok("T", 5), tok("Comp", 6)})
    rule = ext.make_selectional_merge("D", ordered=False)
    with ext.unordered_triggers():
        _, finals, _ = ext.explore(la, rule)
        bad = []
        for X in finals:
            for p in all_paths(X):
                if (isinstance(p[-1], cs.LIToken) and p[-1].li.name == "T"
                        and len(p) >= 2):
                    comp = complement_of(p[-1], p[-2])
                    if comp is not None and "D" in ext.category_features(comp):
                        bad.append(X)
    assert bad
    _, ranked, _ = ext.explore(la, ext.make_selectional_merge("D"))
    assert len(finals) > len(ranked)


# =====================================================================
# Successive-cyclic wh-movement
# =====================================================================

def test_successive_cyclic_wh():
    d = dv.successive_cyclic_wh()
    assert _pf(_final(d)) == "who you think John will see"
    assert all(v for k, v in d.check().items() if k != TRANSFER_NTC_KEY)


def _chunks(d):
    """The pair each Cyclic-Transfer step plugged in, in order."""
    out = []
    for i, s in enumerate(d.steps):
        if s.op == "Cyclic-Transfer":
            (root,) = tuple(d.steps[i].stage.w)
            path = cs.phase_complement_path(root)
            out.append(path[-1])
    return out


def test_embedded_clause_has_its_own_vp_phase():
    """John is the external argument of `see`: merged in Spec,v*P and raised
    to Spec,TP of `will`.  The embedded v*P is a phase, so its VP is
    transferred first (`see`), then the embedded TP (`John will see`)."""
    d = dv.successive_cyclic_wh()
    assert [_pf(c) for c in _chunks(d)] == ["see", "John will see",
                                           "think John will see"]
    n = dv.successive_cyclic_wh(cls=NTCDerivation)
    john = tok("John", 3)
    (p_low,) = [p for p in positions(john, n.root) if is_nonfinal_occurrence(p, n.root)]
    vstar_p = p_low[-2]                                     # {John3, v*'}
    assert label(vstar_p).li.name == "v*_edge"              # John's first Merge is with v*
    assert specifier_of(next(m for m in vstar_p if m != john), vstar_p) == john


def test_wh_is_trapped_without_the_intermediate_edge():
    assert "not contained in the root" in dv.wh_trapped_at_the_phase_edge()


def test_who_has_five_occurrences_one_final():
    d = dv.successive_cyclic_wh(cls=NTCDerivation)      # structure never modified
    ps = positions(tok("who", 1), d.root)
    # in situ, embedded v* edge, embedded Spec,CP, matrix v* edge, matrix Spec,CP
    assert len(ps) == 5
    assert sum(1 for p in ps if not is_nonfinal_occurrence(p, d.root)) == 1


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

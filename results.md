# Results: running Collins & Stabler (2016)

All numbers below are produced by `tables.py` (which writes the three CSVs in
this directory), `extensions.py` and `derivations.py`.  The checks are in
`test_cs2016.py` (55 tests) and `test_sentences.py` (21 tests), all passing.

Definition and theorem numbers are those of the 2016 journal version.  An
earlier version of this project followed the December 2011 manuscript; the
section "What changed from 2011" at the end records what moving to 2016 did
to the results.

## 1. Remnant movement and the plug-back-in model (§11, examples (20)–(21))

In 2016, finality (D40) is structural: `A ∈ {A,B}` is non-final in a phase if
some `C` in the phase has `A` as a member and contains `{A,B}`.  This
correctly makes *John* non-final inside **both** copies of the moved remnant
in (20d), because TP has *John* as a member and contains `{John, to win}`.
So remnant movement within one phase works with the single version of
Cyclic-Transfer (D36). A second version is no longer needed.

The paper then argues that the plug-back-in model is in serious trouble once
the remnant crosses a phase, as in (21).  The implementation confirms this
mechanically:

| derivation | plug-back-in (D36–D38) | §12, occurrence reading | §12, object reading |
|---|---|---|---|
| remnant_movement (20) | how likely to win John is | how likely to win John is | how likely to win John is |
| remnant_across_phases (21) | **how likely John to win you think that John is** | how likely to win you think that John is | (not derivable) |
| successive_cyclic_wh | who you think John will see | who you think John will see | (not derivable) |
| you_wonder_who_john_will_see | you wonder who John will see | you wonder who John will see | (not derivable) |
| who_does_sue_think_fell | who Sue think fell | who Sue think fell | (not derivable) |
| every other derivation | identical in all three columns | | |

(`transfer_regime_comparison.csv` has every row.)

* Under plug-back-in, once the embedded TP has been replaced by its interface
  pair, nothing at the matrix phase contains `{John, to win}` and has *John*
  as a member. *John* becomes final again and is pronounced twice.  The
  derivation is licensed at every step and still **converges** (D42–D44): the
  convergence definitions cannot see the error.
* The same failure arises inside a single phase, because D38 also licenses
  Cyclic-Transfer at (20d) followed by Transfer. That derivation yields
  `how likely John to win John is`
  (`test_the_same_failure_inside_one_phase`).
* Transferring at (20c), before the remnant moves, makes the remnant
  movement itself impossible (T14), as the paper says.

## 2. The §12 NTC-respecting alternative

The paper only sketches §12 (the formal version is in an appendix the authors
did not publish).  We implemented it as described: Transfer extends two
functions PF and LF, the transferred objects are their domain, and "the
accessible parts of workspace W are given by W minus those already
transferred" (`NTCDerivation`).

Confirmed:

* **The NTC is restored.** T8 fails at every Transfer step under the
  plug-back-in model and holds at every one under §12.
* **D37 is unnecessary.** The workspace holds only tokens and sets of them,
  so D7 suffices.
* **The PIC still holds**, but by stipulation (accessibility), as the paper
  says.
* **It solves (21).** The structure is intact, so D40 still sees the
  embedded TP, and *John* is pronounced once.

Under-determined: **what "W minus those already transferred" removes.**  Read
per occurrence (an occurrence is inaccessible iff its path passes through a
transferred object), everything works.  Read per object (an object is
inaccessible iff it is contained in a transferred object), any phrase that has
moved to a phase edge also has an occurrence inside the transferred
complement. It therefore becomes inaccessible, and successive-cyclic
movement, including (21) itself, is underivable.

Also under-determined: **the stage format.** D10 stages are `<LA, W>`. §12
moves Transfer's effect into PF and LF, which the stage does not contain. So a
§12 Transfer step repeats the previous stage, and D38 rejects the sequence.
D42–D44, which require `W_n = {<PHON,SEM>}`, do not apply.  The repair is
definitional: make the stage `<LA, W, PF, LF>`.

## 3. The Chain-based digression and Theorem 4 (§5)

§5 defines a Chain-based system (D7′, D13′–D16′) with no indices, in which
an internally merged set is annotated with the path to the moved item.
Theorem 4 claims a one-to-one, onto, structure-preserving correspondence
between token-based objects up to renumbering ([T(Lex)], excluding merges of
renumberings) and Chain-based objects (C(Lex)).  The proof is in the
unpublished appendix.

We compared both sets exhaustively for the lexicon {John, see} up to five
Merge nodes, mapping each token object to the Chain object with the same
structure and the same path (`theorem4_check.csv`):

| D14′(c) | size ≤ | [T(Lex)] | C(Lex) | token classes with no image | with several images | bijection |
|---|---:|---:|---:|---:|---:|:-:|
| as we read it | 2 | 7 | 7 | 0 | 0 | yes |
| as we read it | 3 | 25 | 23 | 2 | 0 | **no** |
| as we read it | 5 | 703 | 437 | 272 | 6 | **no** |
| dropped | 2 | 7 | 7 | 0 | 0 | yes |
| dropped | 3 | 25 | 27 | 0 | 2 | **no** |
| dropped | 5 | 703 | 1097 | 0 | 224 | **no** |

* The locality condition (c) is garbled in print. It quantifies over every
  `i < k`, which includes B's own mother, so read literally it blocks every
  internal Merge, the paper's own (7′) included.  We read it as `i < k−1`:
  the path may not pass a higher occurrence of B.
* **With (c):** the token system can move a lower token across a higher token
  of the same lexical item, as in `{see2, {see3, {John1, see2}}}`. That
  object is derivable (we build it with the driver), but in the Chain system
  the two *see*s are the same object and (c) forces the higher one to be
  chosen.  Remnant configurations also go wrong the other way. When an item
  sits inside both copies of a moved phrase, neither occurrence c-commands
  the other, (c) allows both paths, and one token object gets two Chain
  objects.
* **Without (c):** the Chain system records *which* occurrence of an
  already-moved item is re-merged, and the token system does not (the paper
  says so: "the question … never arises").  So one token object gets
  several Chain objects.

Under every reading of (c) we could construct, the natural correspondence
fails from size 3 on.  We cannot rule out that the unpublished proof uses a
different correspondence, but it would have to be one that ignores the
paths.

## 4. Selectional Merge, ranked and unranked triggers

Triggered Merge (D27) licenses Merge(A,B) whenever Triggers(A) is non-empty and
Triggers(B) is empty. It never asks whether the trigger feature *matches* B.
`extensions.py` adds the match.  Every complete derivation (D15) from
{see1, Chris2, v*3, John4, T5, Comp6}:

| Merge rule | derivations | objects | stages | PF strings | T5 T6 T8 T9 |
|---|---:|---:|---:|---:|:-:|
| D27 Triggered Merge | 6,267,280 | 648 | 4,072 | 6 | all hold |
| + selection (ranked triggers) | 55,968 | 12 | 280 | 6 | all hold |
| + selection (ranked), EPP needs D | 27,984 | 6 | 178 | 4 | all hold |
| + selection (unranked triggers) | 171,424 | 24 | 448 | 6 | all hold |
| + selection (unranked), EPP needs D | 85,712 | 12 | 304 | 4 | all hold |

* **The general theorems survive every rule.**  T5, T6, T8 and T9 follow from
  the stage/workspace format (D10, D14), not from what licenses a Merge.
* **Which trigger feature D26 checks never matters to the axioms.**  D26
  leaves it open, and under D27 only the *number* of remaining triggers
  matters. The ranked and unranked policies give identical derivations under
  plain D27 (tested).
* **With selection, it does matter, and 2016 assumes the unranked case.**
  §7 says trigger features are *not* ordered, and asks what then prevents
  `[TP vP [T′ T DP]]`. Its answer is that NTC would block the DP moving to
  the complement of T.  For an externally merged DP nothing blocks it.
  Unranked selection doubles the objects (24 vs 12). Every one of the 12
  extra objects has a head whose EPP took a DP as its *complement* and whose
  selection feature was then satisfied by a specifier: 4 have
  `[TP vP [T′ T DP]]`, the paper's own example, and 8 have the same pattern
  one phase down, `[vP VP [v′ v* DP]]`.

## 5. Successive-cyclic wh-movement (added)

`successive_cyclic_wh` derives *Who do you think John will see*.  *John* is
the external argument of *see*: it is merged in the embedded Spec,v*P and
raises to Spec,TP of *will*.  The embedded v*P is a phase whose VP is
transferred before *will* embeds it, so `who1` must first move to the
embedded v* edge.  It ends with five occurrences (in situ, embedded v* edge,
embedded Spec,CP, matrix v* edge, matrix Spec,CP), and exactly one is final
(D40).  Without the step to the
matrix v* edge, Cyclic-Transfer at v*P buries `who` in the transferred VP and
the final movement is refused (T14).  Successive cyclicity is forced by
D35/D36/D38, not stipulated.

## What changed from 2011

* Numbering throughout. For example, Triggers D27→D26, Triggered Merge
  D28→D27, Label D29→D28, strong phase D38→D35, TransferPF D42→D41, PIC
  T13→T14, and NTC T7→T8.
* D14 is now the derivation itself (2011's D14/D22/D23 merged). LA_n = {} and
  a single root are D15.
* D35: a strong phase must be a maximal projection. D38: Transfer is barred
  while an embedded phase's complement is untransferred.  The old code did
  not check the second condition; it now does, and all derivations satisfy
  it.
* **D40 finality replaced 2011's c-command definition.** This is why D36′
  (Cyclic-Transfer of a lower copy), D42′, D42″ and D36″ clause (ii) are
  gone. The earlier finding about D36″ (ii) no longer applies, because 2016
  has no such clause.
* §5 (chains, Theorem 4) is new in 2016.
* 2016 states that trigger features are unordered. The old code's ranking is
  kept only to name which feature is checked, and is shown above to be inert
  under D27.

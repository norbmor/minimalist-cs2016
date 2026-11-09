# An executable Collins & Stabler (2016)

A direct implementation of the axiomatization in Collins, Chris & Edward Stabler
(2016), *A Formalization of Minimalist Syntax*, **Syntax** 19(1): 43–78
(DOI 10.1111/synt.12117; `Collins2016Formalization.pdf`).

All definition (D) and theorem (T) numbers follow the 2016 journal version.
The project was first written against the December 2011 manuscript
(`stabler_11_A-Formalizatio.pdf`), which numbers things differently and
contains definitions the published paper dropped (D36′, D36″, D42′, D42″);
`results.md` lists what changed.

The design goal is transcription, not re-engineering: every definition and
theorem has a named counterpart in `cs2016.py`, tagged with its number, so
that the code can be read against the paper line by line.  Nothing is
enforced that the paper does not state. In particular, `Merge` has no
category-matching check, because D27 checks only the trigger / no-trigger
asymmetry.

## Files

| file | contents |
|---|---|
| `cs2016.py` | the axiomatization: D1–D44, D7′ and D13′–D16′, T1–T14, a `Derivation` driver that validates every step against D14/D38, and the §12 alternative (`NTCDerivation`) |
| `derivations.py` | a lexicon and the paper's examples (6)/(8), (7), (15), (16)/(17), (18), (19)/(20), (21), plus three added derivations |
| `extensions.py` | selectional Merge, with ranked and unranked trigger features, and an enumerator over all complete derivations from a lexical array |
| `tables.py` | regenerates the three CSV tables |
| `test_cs2016.py` | 55 checks, one per definition cluster, theorem, paper example or finding (`python test_cs2016.py`, or pytest) |
| `sentences.py` | seven further constructions on an extended lexicon: raising, an embedded question, a ditransitive, an affirmative/negated minimal pair, an embedded declarative (*Sue thinks John fell*), and long-distance subject wh-movement (*Who does Sue think fell*) |
| `test_sentences.py` | 21 checks, one per property those sentences exhibit, plus a smoke test that draws every registered derivation |
| `results.md` | what the implementation shows, with the measured numbers |
| `paper.tex` | a write-up (`python figures.py`, then `pdflatex paper.tex` twice) |
| `derivation_report.txt`, `sentence_report.txt` | stage-by-stage traces with checks, PF, LF and convergence |
| `merge_rule_comparison.csv`, `transfer_regime_comparison.csv`, `theorem4_check.csv` | the tables in `results.md` |
| `figures.py` | draws every figure: the four `paper.tex` uses, and a tree for every registered derivation under either model of Transfer; the only part that needs matplotlib |
| `figures/` | `python figures.py --all` and `--intact --all`: 17 trees under the plug-back-in model, 17 under section 12 |
| `remnant_derivation.png` | (20d) against (21): *John* is non-final in one phase, final again once the embedded TP is plugged back in |
| `successive_cyclic_wh.png` | the five occurrences of *who*, and what happens when the matrix v* edge step is skipped |
| `mary_not_praise_john.png`, `you_wonder_who_john_will_see.png` | trees used in `paper.tex` |

## Definition map (2016 numbering)

**§2 Preliminaries.** `UniversalGrammar` (D1), `LexicalItem` (D2), `Lexicon`
(D3), `ILanguage` (D4), `LIToken` (D5), `lexical_array` (D6),
`is_syntactic_object` (D7, revised as D37), `immediately_contains` (D8),
`contains` (D9).

**§3 Workspaces, Select, Merge.** `Stage` (D10), `is_root` (D11), `select`
(D12), `merge` (D13), `derives_by_select` / `derives_by_merge` /
`is_derivation` (D14), `derived_object` (D15).  D14 is now the definition of
a derivation. It does not require LA_n = {} or a single root; that is D15.

**§4 Occurrences.** `positions` (D16, D17), `occ_immediately_contains` (D18),
`theorem1_holds` (T1), `are_sisters` (D19), `sister_positions` (D20),
`theorem2_holds` (T2), `c_commands` / `asymmetrically_c_commands` (D21),
`occ_c_commands` (D22), `theorem3_holds` (T3).

**§5 Chains.** `ChainSO` (D7′), `chain_positions` (D16′), `chain_merge`
(D13′), `is_chain_derivation` (D14′), `chain_derivable` (D15′),
`theorem4_report` (T4, checked on bounded fragments).

**§6 General properties.** `is_derivable_workspace` (D23),
`is_binary_branching` (D24, T5), `unique_root_occurrences` (T6),
`two_occurrences_iff_internal_merge` (T7), `satisfies_ntc` (T8),
`satisfies_extension` (T9), `satisfies_inclusiveness` (T10); T11 (Local
Economy) holds by construction.

**§7 Labels.** `trigger_features` (D25), `triggers` (D26), `triggered_merge`
(D27; T12 is its failure mode), `label` (D28, T13), `is_maximal_projection`
(D29), `is_minimal_projection` (D30), `is_intermediate_projection` (D31),
`complement_of` (D32), `specifier_of` (D33).

**§8 Transfer.** `transfer` (D34), `is_strong_phase` (D35), `cyclic_transfer`
(D36), D37 in `is_syntactic_object`, `derives_by_transfer` and
`untransferred_inner_phases` (D38), `pic_blocks` (T14).

**§9–10.** `transfer_lf` (D39), `is_final` (D40), `transfer_pf` (D41).

**§12 NTC-respecting Transfer.** `NTCStage`, `is_accessible`,
`cyclic_transfer_ntc`, `transfer_pf_ntc`, `transfer_lf_ntc`, `transfer_ntc`,
and the `NTCDerivation` driver.

**§13 Convergence.** `converges_at_ci` (D42), `converges_at_sm` (D43),
`converges` (D44).

## Stipulations

The paper leaves these open; the code marks each `# STIPULATION`.

1. **Which trigger feature D26(ii) checks.** The paper says only "a particular
   one, determined by B and C", and does not order trigger features.  The
   default checks the lowest-ranked one (`cs2016.DISCHARGE`).  Under D27 the
   choice never affects derivability, because only the *number* of remaining
   triggers matters (tested).  It matters only once selection is added
   (`extensions.py`).
2. **D38's Transfer clause does not constrain LA_i+1.** We require it to
   equal LA_i, as in derive-by-Merge.
3. **"Replacing A" in D36** is read positionally: the complement occurrence
   is replaced.
4. **The locality condition D14′(c)** is garbled in print (literally it
   blocks every internal Merge). We read it as "the path does not pass a
   higher occurrence of B".
5. **§12 accessibility.** "W minus those already transferred" is read per
   occurrence by default.  The per-object reading is available as
   `NTCDerivation(reading="object")`, and it breaks successive-cyclic
   movement.
6. **Display metadata.** `LexicalItem.name` and `.cat` exist only for
   printing.

## What the code reproduces, and what it finds

* **Remnant movement in one phase works with plain D36** (19)/(20), because
  D40 makes *John* non-final in both copies of the moved DegP. PF is
  `how likely to win John is`.
* **The plug-back-in model fails across phases** (21). After the embedded TP
  is replaced by its interface pair, *John* is final again, and PF is
  `how likely John to win you think that John is`. The derivation still
  converges.  The §12 alternative gives `how likely to win you think that
  John is`.
* **Cyclic-Transfer violates the NTC** (T8 fails at every Transfer step)
  under plug-back-in, and respects it under §12.
* **Theorem 4 fails on bounded fragments** under both readings of D14′(c) we
  tested, from three Merge nodes on (`theorem4_check.csv`).
* **Selection** cuts 6,267,280 derivations over 648 objects to 55,968 over
  12, and T5/T6/T8/T9 hold throughout.  With unranked triggers, as 2016
  assumes, it admits 24 objects, including the `[TP vP [T′ T DP]]` that §7
  worries about.

Details and numbers are in `results.md`.

## Usage

```python
from derivations import LEX
from cs2016 import Derivation, labelled_bracket

d = Derivation(LEX, [LEX.token("fall", 1), LEX.token("John", 2),
                     LEX.token("T_V", 3), LEX.token("Comp", 4)])
d.select("fall", 1).select("John", 2).merge_roots()
d.select_and_merge("T_V", 3)
d.internal_merge(LEX.token("John", 2))
d.select_and_merge("Comp", 4)
print(labelled_bracket(d.root))   # [CP Comp4 [TP John2 [T' T_V3 [VP fall1 <John2>]]]]
d.transfer()                      # D38(a): Transfer(CP, CP)
d.check()
```

Every operation asserts that the previous stage derives the new one by a
clause of D14/D38, so a `Derivation` cannot contain an unlicensed step.
Illegal moves raise with the number of the definition they violate.  For
example, `triggered_merge(Chris, see)` reports D27, selecting outside the
lexical array reports D12, and transferring a phase that contains an
untransferred phase reports D38.

```bash
python test_cs2016.py && python test_sentences.py
python derivations.py > derivation_report.txt
python sentences.py   > sentence_report.txt
python tables.py                       # the three CSVs
python figures.py                      # every figure paper.tex includes (4 PNGs)
python figures.py --all                # a tree for every derivation -> figures/
python figures.py --intact --all       # the same under section 12 Transfer
python figures.py john_fell --out DIR  # chosen trees, anywhere
python figures.py --list
```

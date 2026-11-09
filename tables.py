"""
tables.py -- regenerate the three CSV tables reported in results.md.

    python tables.py

    merge_rule_comparison.csv       extension 1: every complete derivation (D15)
                                    from a six-token array under each Merge rule
    transfer_regime_comparison.csv  section 11/12: PF under the plug-back-in model
                                    and under the section 12 alternative
    theorem4_check.csv              section 5: [T(Lex)] against C(Lex), by size
"""
from __future__ import annotations

import csv
import os
import sys
from functools import partial

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import cs2016 as cs
import derivations as dv
import extensions as ext
import sentences as sn
from cs2016 import NTCDerivation, TRANSFER_NTC_KEY, pf_string
from derivations import LEX


def merge_rules(path: str) -> None:
    T = LEX.token
    la = [T("see", 1), T("Chris", 2), T("v*", 3), T("John", 4), T("T", 5), T("Comp", 6)]
    res = ext.compare(LEX, la)
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["rule", "derivations", "complete_objects", "stages",
                    "distinct_pf_strings", "T5", "T6", "T8", "T9"])
        for name, r in res.items():
            th = r["theorems"]
            w.writerow([name, r["derivations"], r["distinct complete objects"],
                        r["stages visited"], len(r["pf strings"]),
                        th["T5 binary branching"], th["T6 unique root occurrences"],
                        th["T8 No Tampering"], th["T9 Extension (at Merge)"]])


def _pf_or_error(fn, cls) -> str:
    try:
        d = fn(cls=cls)
    except (ValueError, AssertionError):
        return "(not derivable)"
    x = d.interfaces if isinstance(d, NTCDerivation) else next(iter(d.stages[-1].w))
    return pf_string(x.pf)


def transfer_regimes(path: str) -> None:
    fns = [dv.john_fell, dv.john_sees_chris, dv.crashing, dv.remnant_movement,
           dv.remnant_across_phases, dv.successive_cyclic_wh] + list(sn.ALL.values())
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["derivation", "pf_plug_back_in", "pf_sec12_occurrence",
                    "pf_sec12_object", "ntc_at_transfer_plug_back_in",
                    "ntc_at_transfer_sec12"])
        for fn in fns:
            w.writerow([
                fn.__name__,
                _pf_or_error(fn, cs.Derivation),
                _pf_or_error(fn, NTCDerivation),
                _pf_or_error(fn, partial(NTCDerivation, reading="object")),
                fn().check()[TRANSFER_NTC_KEY],
                fn(cls=NTCDerivation).check()[TRANSFER_NTC_KEY],
            ])


def theorem4(path: str, kmax: int = 5) -> None:
    items = [LEX.by_name("John"), LEX.by_name("see")]
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["locality_D14c", "max_size", "token_classes", "chain_objects",
                    "token_classes_with_no_chain_image",
                    "token_classes_with_several_chain_images",
                    "chain_objects_without_preimage", "bijection"])
        for loc in (True, False):
            for k in range(1, kmax + 1):
                r = cs.theorem4_report(items, k, loc)
                bad = r["token objects without a unique chain image"]
                w.writerow([loc, k, r["token classes"], r["chain objects"],
                            sum(1 for _, c in bad if not c),
                            sum(1 for _, c in bad if len(c) > 1),
                            len(r["chain objects with no token preimage"]),
                            r["bijection"]])


if __name__ == "__main__":
    for name, fn in (("merge_rule_comparison.csv", merge_rules),
                     ("transfer_regime_comparison.csv", transfer_regimes),
                     ("theorem4_check.csv", theorem4)):
        fn(os.path.join(_HERE, name))
        print("wrote", name)

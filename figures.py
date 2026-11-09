"""
figures.py -- every figure in this project, drawn from validated derivations.

    python figures.py                  # every figure paper.tex includes
    python figures.py --all            # a tree for every registered derivation,
                                       #   written to figures/
    python figures.py --intact ...     # the same, under section 12 Transfer
                                       #   (structure never replaced)
    python figures.py john_fell ...    # one tree per named derivation
    python figures.py --list           # the names it knows
    python figures.py --out DIR ...    # write somewhere else

`derivation_figure(fn)` draws any derivation function that takes `cls=`,
including the ones in `sentences.py`; the two figures above are hand-composed
because they each make a point that needs two panels and an annotation.

Nothing here is part of the formalization: every tree is read off a validated
`Derivation` object with `label` (D28), `ordered_children` (D41b) and
`is_nonfinal_occurrence` (D40), so a figure cannot show a structure the axioms
did not build.  Only the display names and the layout are stipulated.

matplotlib is the one dependency; the rest of the project is standard library.
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

import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

import derivations as dv
from cs2016 import (
    Derivation, LFObject, LIToken, NTCDerivation, Transferred, fmt_lf,
    converges_at_ci, converges_at_sm, is_maximal_projection, is_nonfinal_occurrence,
    label, ordered_children, pf_string, positions,
)
from derivations import LEX

try:                                   # optional: the extra constructions
    import sentences as sn
except ImportError:                    # pragma: no cover
    sn = None

# ---------------------------------------------------------------------
# Style.  Three font sizes, mapped to role: node labels, annotations,
# captions; panel letters are the one exception.
# ---------------------------------------------------------------------

BASE, SMALL, TINY = 9.5, 8.5, 8.0
INK = "#1a1a1a"          # ordinary nodes and branches
MOVED = "#c0392b"        # the token whose occurrences the figure is about
TRANSFERRED = "#0f7b7b"  # output of Transfer (D34) -- not a syntactic object
FADED = "#9a9a9a"        # a non-final phrasal occurrence, and side notes

RC = {
    "font.family": "DejaVu Sans",
    "font.size": BASE,
    "figure.dpi": 160,
    "savefig.dpi": 160,
    "savefig.bbox": None,
    "text.color": INK,
}

# Display names (stipulation: no definition refers to them).  A lexical item
# with a phonological form is shown by that form, a silent one by a short
# conventional name for its category.
DISPLAY = {"Comp": "C", "Comp_Q": "C", "Comp_edge": "C", "v*": "v*", "v*_edge": "v*",
           "T": "T", "T_V": "T", "T_Neg": "T"}

_SUBSCRIPT = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


def _sub(k: int) -> str:
    return str(k).translate(_SUBSCRIPT)


def _token_name(t: LIToken) -> str:
    li = t.li
    form = "".join(f.name for f in li.phon)
    return (form or DISPLAY.get(li.name, li.name)) + _sub(t.k)


def _phrase_tag(X: Any, root: Any) -> str:
    try:
        li = label(X).li
    except ValueError:              # D13 output: no label (D28), drawn as in (3)
        return "*"
    cat = li.cat or li.name
    try:
        maximal = is_maximal_projection(X, root)
    except ValueError:              # an unlabelled (D13) mother projects nothing
        maximal = True
    return cat + "P" if maximal else cat + "'"


def _transferred_text(X: Transferred) -> str:
    pf = "-".join(f.name for f in X.pf) or "∅"
    if not isinstance(X.lf, LFObject):
        return f"⟨{pf}⟩"        # a complex LF does not fit beside the PF
    lf = re.sub(r"_(\d+)$", lambda m: _sub(int(m.group(1))), fmt_lf(X.lf))
    return f"⟨{pf}, {lf}⟩"


# ---------------------------------------------------------------------
# From a syntactic object to a drawable tree
# ---------------------------------------------------------------------

@dataclass
class Node:
    text: str
    color: str = INK
    children: List["Node"] = field(default_factory=list)
    x: float = 0.0
    depth: int = 0


def to_node(root: Any, path: Sequence[Any], highlight: Set[LIToken],
            depth: int = 0) -> Node:
    """Read one occurrence of a syntactic object off `root` as a drawable node.

    A non-final occurrence (D40) of a *phrase* is collapsed to its label: it is
    a copy, and expanding it twice would misrepresent the single object the
    workspace holds.  Unlabelled (D13) sets are drawn as `*`, as in the
    paper's (3) and (5), and never collapsed.
    """
    X = path[-1]
    if isinstance(X, Transferred):
        return Node(_transferred_text(X), TRANSFERRED, depth=depth)
    if isinstance(X, LIToken):
        text = _token_name(X)
        colour = MOVED if X in highlight else INK
        if _nonfinal(tuple(path), root):
            text = f"⟨{text}⟩"
        return Node(text, colour, depth=depth)
    if _nonfinal(tuple(path), root):
        return Node(f"({_phrase_tag(X, root)})", FADED, depth=depth)
    try:
        order = ordered_children(X)
    except ValueError:
        order = sorted(X, key=lambda m: (isinstance(m, frozenset), repr(m)))
    kids = [to_node(root, tuple(path) + (k,), highlight, depth + 1) for k in order]
    return Node(_phrase_tag(X, root), INK, kids, depth=depth)


def _nonfinal(path, root) -> bool:
    """D40, guarded: an unlabelled D13 object has no finality (D41 presupposes
    labels), so nothing in it is marked."""
    try:
        return is_nonfinal_occurrence(path, root)
    except ValueError:
        return False


# ---------------------------------------------------------------------
# Layout and drawing
# ---------------------------------------------------------------------

def _layout(node: Node, x0: float = 0.0, unit: float = 0.52) -> float:
    """Assign x positions; a leaf reserves at least the width of its label."""
    if not node.children:
        w = max(1.0, (len(node.text) + 1.2) * unit)
        node.x = x0 + w / 2
        return x0 + w
    cursor = x0
    for kid in node.children:
        cursor = _layout(kid, cursor, unit)
    node.x = (node.children[0].x + node.children[-1].x) / 2
    return cursor


def _walk(node: Node):
    yield node
    for kid in node.children:
        yield from _walk(kid)


def draw_tree(ax, root_node: Node, x_offset: float = 0.0,
              y_offset: float = 0.0, row: float = 1.0) -> None:
    for n in _walk(root_node):
        y = y_offset - n.depth * row
        for kid in n.children:
            ax.plot([n.x + x_offset, kid.x + x_offset],
                    [y - 0.23 * row, y - row + 0.26 * row],
                    color=FADED if kid.color == FADED else INK,
                    lw=0.8, zorder=1, solid_capstyle="round")
        ax.text(n.x + x_offset, y, n.text, ha="center", va="center",
                fontsize=BASE, color=n.color, zorder=2)


def depth_of(node: Node) -> int:
    return max(n.depth for n in _walk(node))


def tree_panel(ax, node: Node, title: str,
               letter: Optional[str] = None, note: str = "",
               note_color: str = FADED, note_xy=(0.99, 0.93),
               caption: str = "", caption_y: Optional[float] = None,
               ylim=None, pad: float = 1.6) -> Node:
    width = _layout(node)
    draw_tree(ax, node)
    depth = depth_of(node)
    ax.set_xlim(-pad, width + pad)
    ax.set_ylim(ylim if ylim is not None else (-depth - 1.4, 1.5))
    ax.axis("off")
    ax.set_title(title, fontsize=BASE, loc="left", pad=10,
                 x=0.0 if letter is None else 0.03)
    if letter is not None:
        ax.text(-0.01, 1.06, letter, transform=ax.transAxes, fontsize=BASE + 2.5,
                fontweight="bold", ha="right", va="bottom")
    if note:
        ax.text(*note_xy, note, transform=ax.transAxes, fontsize=SMALL,
                ha="right", va="top", color=note_color, linespacing=1.5)
    if caption:
        ax.text(-pad * 0.6, caption_y if caption_y is not None else -depth - 1.0,
                caption, fontsize=SMALL, ha="left", va="top", color=INK,
                linespacing=1.6)
    return node


# ---------------------------------------------------------------------
# The two figures
# ---------------------------------------------------------------------

def remnant_figure(path: str = "remnant_derivation.png"):
    """(20d) and (21): remnant movement in one phase, and across two."""
    john = {LEX.token("John", 1)}
    one = dv.remnant_movement()
    two = dv.remnant_across_phases()
    a = last_syntactic_root(one)                  # (20d), before Transfer
    b = last_syntactic_root(two)                  # (21), before the final Transfer
    node_a = to_node(a, (a,), john)
    node_b = to_node(b, (b,), john)
    deep = max(depth_of(node_a), depth_of(node_b))
    ylim, cap_y = (-deep - 2.3, 1.5), -deep - 1.1
    ntc = pf_string(dv.remnant_across_phases(cls=NTCDerivation).interfaces.pf)

    fig = plt.figure(figsize=(15.0, 6.0))
    gs = fig.add_gridspec(1, 2, width_ratios=(1, 1.35), wspace=0.06,
                          left=0.012, right=0.988, top=0.82, bottom=0.05)
    ax1, ax2 = fig.add_subplot(gs[0]), fig.add_subplot(gs[1])

    tree_panel(
        ax1, node_a,
        "(20d) One phase: John\u2081 is non-final in both copies of DegP", letter="a",
        note="\u27e8X\u27e9  non-final (D40): some C containing\n"
             "{X, Y} also has X as a member",
        caption="TP has John\u2081 as a member and contains {John\u2081, to win},\n"
                "so Transfer(CP, CP) yields PF  =  " + _pf(one),
        caption_y=cap_y, ylim=ylim)
    tree_panel(
        ax2, node_b,
        "(21) Two phases, plug-back-in: the embedded TP is gone, "
        "so John\u2081 is final again",
        letter="b",
        note="\u27e8\u2026\u27e9  output of Cyclic-Transfer (D36),\n"
             "not a syntactic object (D37)",
        note_color=TRANSFERRED,
        caption="plug-back-in (D36\u2013D38):  PF  =  " + _pf(two) +
                "\nsection 12 (structure kept):  PF  =  " + ntc,
        caption_y=cap_y, ylim=ylim)

    fig.suptitle("Remnant movement and the plug-back-in model of Transfer\n"
                 "(Collins & Stabler 2016, \u00a711, examples (20) and (21))",
                 fontsize=BASE + 0.5, x=0.012, ha="left", y=0.985,
                 va="top", linespacing=1.6)
    fig.savefig(path)
    plt.close(fig)
    return path


def wh_figure(path: str = "successive_cyclic_wh.png"):
    """(21)+matrix clause -- why the intermediate edge step is forced."""
    who = {LEX.token("who", 1)}
    # Section 12 Transfer never modifies the structure, so every landing site
    # is still visible in the final object.
    full = dv.successive_cyclic_wh(cls=NTCDerivation).root
    trapped = dv.successive_cyclic_wh(escape_the_matrix_vP=False,
                                      stop_after_matrix_vP=True).root
    node_a = to_node(full, (full,), who)
    node_b = to_node(trapped, (trapped,), who)
    ylim = (-depth_of(node_a) - 1.6, 1.5)        # one vertical scale for both

    fig = plt.figure(figsize=(13.4, 7.6))
    gs = fig.add_gridspec(1, 2, width_ratios=(1.75, 1), wspace=0.05,
                          left=0.015, right=0.985, top=0.86, bottom=0.04)
    ax1, ax2 = fig.add_subplot(gs[0]), fig.add_subplot(gs[1])

    tree_panel(ax1, node_a,
               "Five occurrences of who\u2081; only the highest is spelled out",
               letter="a", ylim=ylim)
    ax1.text(0.99, 0.95,
             "in situ  \u2192  embedded v* edge  \u2192  embedded Spec,CP\n"
             "     \u2192  matrix v* edge  \u2192  matrix Spec,CP",
             transform=ax1.transAxes, fontsize=SMALL, ha="right", va="top",
             color=MOVED, linespacing=1.6)
    ax1.text(0.99, 0.74,
             "Section 12 Transfer leaves the structure\n"
             "intact, so every landing site stays visible."
             f"\n\nPF  =  {_pf(dv.successive_cyclic_wh())}",
             transform=ax1.transAxes, fontsize=SMALL, ha="right", va="top",
             color=INK, linespacing=1.6)

    tree_panel(ax2, node_b,
               "Without the matrix v* edge step, who\u2081 ends up inside\n"
               "the transferred complement", letter="b",
               caption="who\u2081 is no longer a term of the workspace,\n"
                       "so wh-movement is impossible.",
               caption_y=-depth_of(node_b) - 1.0, ylim=ylim)

    fig.suptitle("Successive-cyclic wh-movement must stop at every strong-phase edge",
                 fontsize=BASE + 0.5, x=0.015, ha="left", y=0.985, va="top")
    fig.savefig(path)
    plt.close(fig)
    return path


# ---------------------------------------------------------------------
# Any derivation
# ---------------------------------------------------------------------

def _tokens(X, acc=None):
    """Every lexical item token occurring in X (Transferred chunks are opaque)."""
    acc = set() if acc is None else acc
    if isinstance(X, LIToken):
        acc.add(X)
    elif isinstance(X, frozenset):
        for m in X:
            _tokens(m, acc)
    return acc


def moved_tokens(root: Any) -> Set[LIToken]:
    """The tokens with more than one occurrence (D16/D17) -- the ones that moved."""
    return {t for t in _tokens(root) if len(positions(t, root)) > 1}


def last_syntactic_root(d) -> Any:
    """The last single-rooted workspace before Transfer replaced it (D34).

    The same choice `derivations.report` makes for its `structure :` line.
    """
    for step in reversed(d.steps):
        if step.op in ("Merge", "Select") and len(step.stage.w) == 1:
            return next(iter(step.stage.w))
    raise ValueError("no single-rooted syntactic stage in this derivation")


def derivation_figure(fn, path: Optional[str] = None, title: Optional[str] = None,
                      highlight: Optional[Set[LIToken]] = None,
                      intact: bool = False, caption: Optional[str] = None):
    """Draw the derived structure of any derivation function.

    `fn` is a function taking `cls=` -- everything in `derivations.ALL` and
    `sentences.ALL` qualifies.  With `intact=True` it is run under
    `NTCDerivation`, whose Transfer never modifies the workspace, so every
    occurrence stays visible instead of being replaced by its spelled-out
    chunk.

    `highlight` defaults to the tokens with more than one occurrence (D16/D17)
    -- for a moved *phrase* that is every token inside it, which is what
    moved.
    """
    d = fn(cls=NTCDerivation if intact else Derivation)
    root = last_syntactic_root(d)
    node = to_node(root, (root,), moved_tokens(root) if highlight is None else set(highlight))
    width, depth = _layout(node), depth_of(node)

    if caption is None:
        bits = []
        final = next(iter(d.stages[-1].w))
        if getattr(d, "interfaces", None) is not None:
            # section 12: the workspace is untouched; the output is separate,
            # and D42-D44 (stated over W_n) do not apply to it
            bits.append("PF  =  " + pf_string(d.interfaces.pf))
            bits.append("section 12 Transfer: structure kept, D42\u2013D44 not applicable")
        elif hasattr(final, "pf"):
            bits.append("PF  =  " + pf_string(final.pf))
            bad = ([] if converges_at_ci(d.stages) else ["CI (D42)"]) + \
                  ([] if converges_at_sm(d.stages) else ["SM (D43)"])
            bits.append("converges (D44)" if not bad else "CRASHES at " + " and ".join(bad))
        else:
            bits.append("no Transfer step, so PF and convergence (D41\u2013D44) do not apply")
        caption = "\n".join(bits)

    fig = plt.figure(figsize=(max(5.2, width * 0.23), max(3.2, (depth + 3.4) * 0.62)))
    ax = fig.add_axes([0.015, 0.02, 0.97, 0.88])
    if title is None:
        title = REGISTRY.get(fn.__name__, (fn.__name__, None))[0]
        if intact:
            title = title.replace(" (plug-back-in)", "") + "  \u2014  section 12 Transfer"
    tree_panel(ax, node, title,
               caption=caption, caption_y=-depth - 1.0,
               ylim=(-depth - 2.0, 1.4))
    path = path or (fn.__name__ + ".png")
    fig.savefig(path)
    plt.close(fig)
    return path


def _registry() -> Dict[str, Any]:
    """Every curated derivation, by function name."""
    pairs = list(dv.ALL.items()) + (list(sn.ALL.items()) if sn else [])
    return {fn.__name__: (title, fn) for title, fn in pairs}


REGISTRY = _registry()


def _pf(d) -> str:
    (final,) = tuple(d.stages[-1].w)
    return pf_string(final.pf)


# The trees paper.tex includes, besides the two composite figures, and
# whether each is drawn intact (section 12 Transfer, so embedded structure
# stays visible instead of being folded into a transferred chunk).
PAPER_TREES = (("mary_not_praise_john", False),
               ("you_wonder_who_john_will_see", True))


def _main(argv) -> None:
    here = os.path.dirname(os.path.abspath(__file__))
    argv = list(argv)
    out = None
    if "--out" in argv:
        i = argv.index("--out")
        if i + 1 >= len(argv):
            raise SystemExit("--out needs a directory")
        out = argv[i + 1]
        del argv[i:i + 2]
    intact = "--intact" in argv
    argv = [a for a in argv if a != "--intact"]
    if argv == ["--list"]:
        for name, (title, _) in sorted(REGISTRY.items()):
            print(f"{name:30} {title}")
        return
    with plt.rc_context(RC):
        if not argv:
            # everything paper.tex needs, next to paper.tex
            out = out or here
            os.makedirs(out, exist_ok=True)
            for fn in (remnant_figure, wh_figure):
                print("wrote", fn(os.path.join(out, fn.__defaults__[0])))
            for name, intact in PAPER_TREES:
                _, fn = REGISTRY[name]
                print("wrote", derivation_figure(fn, os.path.join(out, name + ".png"),
                                                 intact=intact))
            return
        if argv == ["--all"]:
            names, out = sorted(REGISTRY), out or os.path.join(here, "figures")
        else:
            names, out = argv, out or os.getcwd()
        unknown = [n for n in names if n not in REGISTRY]
        if unknown:
            raise SystemExit(f"unknown derivation(s) {unknown}; try --list")
        os.makedirs(out, exist_ok=True)
        suffix = "_intact" if intact else ""
        for name in names:
            _, fn = REGISTRY[name]
            path = os.path.join(out, name + suffix + ".png")
            print("wrote", derivation_figure(fn, path, intact=intact))


if __name__ == "__main__":
    _main(sys.argv[1:])

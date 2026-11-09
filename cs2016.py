"""
cs2016.py -- an executable formalization of

    Collins, Chris & Edward Stabler (2016).
    "A Formalization of Minimalist Syntax." Syntax 19(1): 43-78.
    DOI: 10.1111/synt.12117

Every public name below is tagged with the number of the definition (D) or
theorem (T) it implements, using the numbering of the 2016 journal version.
Section numbers in the banners are the paper's.  The 2011 manuscript numbered
things differently and contained definitions the published version dropped
(D36', D36'', D42', D42''); none of those is implemented here.

Places where the paper leaves something open and this implementation must
choose are marked  # STIPULATION  and listed in README.md.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass
from functools import lru_cache
from typing import (Any, Callable, Dict, FrozenSet, Iterable, List, Optional,
                    Sequence, Set, Tuple)

# =====================================================================
# 2. Preliminary definitions  (D1-D9)
# =====================================================================

SEM, SYN, PHON = "SEM", "SYN", "PHON"


@dataclass(frozen=True, order=True)
class Feature:
    """A member of one of the universal feature sets PHON-F, SYN-F, SEM-F (D1).

    `trigger` marks a trigger feature in the sense of D25.
    `order` is a rank used only to *name* which trigger feature D26(ii)
    checks; see `triggers`.                                       # STIPULATION
    `interpretable` is read by the convergence definitions (D42, D43).
    """
    name: str
    kind: str = SYN
    trigger: bool = False
    order: int = 0
    interpretable: bool = True

    def __repr__(self) -> str:
        return ("*" if self.trigger else "") + self.name


def sem(*names: str, uninterpretable: Sequence[str] = ()) -> FrozenSet[Feature]:
    bad = set(uninterpretable)
    return frozenset(Feature(n, SEM, interpretable=(n not in bad)) for n in names)


def syn(*names: str) -> FrozenSet[Feature]:
    """Plain (non-trigger) syntactic features."""
    return frozenset(Feature(n, SYN) for n in names)


def trig(*names: str) -> FrozenSet[Feature]:
    """Trigger features (D25), ranked left to right."""
    return frozenset(Feature(n, SYN, trigger=True, order=i) for i, n in enumerate(names))


def pho(*names: str, uninterpretable: Sequence[str] = ()) -> Tuple[Feature, ...]:
    """PHON, a string over PHON-F (D2: PHON is in PHON-F*)."""
    bad = set(uninterpretable)
    return tuple(Feature(n, PHON, interpretable=(n not in bad)) for n in names)


@dataclass(frozen=True)
class LexicalItem:
    """D2. A lexical item is a triple LI = <SEM, SYN, PHON>, where SEM and SYN
    are finite feature sets and PHON is in PHON-F* (a string).

    `name` and `cat` are display metadata only; they are not part of D2.
    """
    sem: FrozenSet[Feature] = frozenset()
    syn: FrozenSet[Feature] = frozenset()
    phon: Tuple[Feature, ...] = ()
    name: str = ""
    cat: str = ""

    def __repr__(self) -> str:
        return self.name or ("/" + "".join(f.name for f in self.phon) + "/")


class Lexicon(frozenset):
    """D3. A lexicon is a finite set of lexical items."""

    def by_name(self, name: str) -> LexicalItem:
        for li in self:
            if li.name == name:
                return li
        raise KeyError(name)

    def token(self, name: str, k: int) -> "LIToken":
        return LIToken(self.by_name(name), k)


@dataclass(frozen=True)
class LIToken:
    """D5. A lexical item token is a pair <LI, k> with k an integer."""
    li: LexicalItem
    k: int

    def __repr__(self) -> str:
        return f"{self.li!r}{self.k}"


def lexical_array(*tokens: LIToken) -> FrozenSet[LIToken]:
    """D6. A lexical array is a finite set of lexical item tokens."""
    return frozenset(tokens)


@dataclass(frozen=True)
class LFObject:
    """Output of TransferLF on a lexical item token: <Sem, k>  (D39a)."""
    sem: FrozenSet[Feature]
    k: int

    def __repr__(self) -> str:
        return (",".join(sorted(f.name for f in self.sem)) or "0") + f"_{self.k}"


@dataclass(frozen=True)
class Transferred:
    """The pair <TransferPF(P,A), TransferLF(P,A)> produced by Transfer (D34)
    and plugged back into the tree by Cyclic-Transfer (D36).

    It is *not* a syntactic object (D37), and that is what makes the PIC a
    theorem (T14).
    """
    pf: Tuple[Feature, ...]
    lf: Any

    def __repr__(self) -> str:
        s = "-".join(f.name for f in self.pf) if self.pf else "0"
        return "<" + s + ", " + fmt_lf(self.lf) + ">"


SO = Any  # LIToken | frozenset[SO] | (a set containing Transferred, via D37ii)


def is_syntactic_object(X: Any) -> bool:
    """D7, as revised by D37.

    X is a syntactic object iff X is a lexical item token, or X is the output
    of Cyclic-Transfer (a set one of whose members is a Transferred pair), or
    X is a set of syntactic objects.  A bare Transferred pair is *not* one.
    """
    if isinstance(X, LIToken):
        return True
    if isinstance(X, frozenset):
        return all(is_syntactic_object(m) or isinstance(m, Transferred) for m in X)
    return False


def immediately_contains(B: SO, A: SO) -> bool:
    """D8. B immediately contains A iff A is a member of B."""
    return isinstance(B, frozenset) and A in B


def contains(B: SO, A: SO) -> bool:
    """D9. B contains A iff B immediately contains A, or B immediately contains
    some C that contains A.  (The transitive closure of membership.)

    The recursion does not descend into a Transferred pair, since it has no
    syntactic objects as members.  D8 and D9 also apply to workspaces.
    """
    return _contains(B, A)


@lru_cache(maxsize=None)
def _contains(B: SO, A: SO) -> bool:
    if not isinstance(B, frozenset):
        return False
    if A in B:
        return True
    return any(_contains(C, A) for C in B if isinstance(C, frozenset))


# =====================================================================
# 3. Workspaces, Select and Merge  (D10-D15)
# =====================================================================

@dataclass(frozen=True)
class Stage:
    """D10. A stage is a pair S = <LA, W>; W is the workspace of S."""
    la: FrozenSet[LIToken]
    w: FrozenSet[SO]

    def __repr__(self) -> str:
        return f"<LA={set(self.la) or '{}'}, W={set(self.w) or '{}'}>"


def is_root(X: SO, s: Stage) -> bool:
    """D11. X is a root in W iff X is in W."""
    return X in s.w


def select(li: LIToken, s: Stage) -> Stage:
    """D12. If A is in LA, Select(A, <LA,W>) = <LA - {A}, W u {A}>."""
    if li not in s.la:
        raise ValueError(f"Select undefined: {li!r} not in the lexical array (D12)")
    return Stage(s.la - {li}, s.w | {li})


def merge(A: SO, B: SO) -> FrozenSet[SO]:
    """D13. Given any two distinct syntactic objects A, B: Merge(A,B) = {A,B}."""
    if A == B:
        raise ValueError("Merge undefined: A and B are not distinct (D13)")
    if not (is_syntactic_object(A) and is_syntactic_object(B)):
        raise ValueError("Merge undefined: argument is not a syntactic object (D7/D37)")
    return frozenset({A, B})


def triggered_merge(A: SO, B: SO) -> FrozenSet[SO]:
    """D27 (Triggered Merge, replacing D13).

    Given syntactic objects A, B where Triggers(A) != {} and Triggers(B) = {},
    Merge(A,B) = {A,B}.  The paper notes that the triggering condition entails
    that A and B are distinct; Theorem 12 (asymmetry) follows immediately.
    """
    if not triggers(A):
        raise ValueError(f"Triggered Merge undefined: Triggers({A!r}) is empty (D27)")
    if triggers(B):
        raise ValueError(f"Triggered Merge undefined: Triggers({B!r}) is non-empty (D27)")
    return merge(A, B)


def _all_contained(A: SO) -> List[SO]:
    """Every syntactic object contained in A (D9), with repetitions."""
    out: List[SO] = []
    if isinstance(A, frozenset):
        for m in A:
            if isinstance(m, Transferred):
                continue
            out.append(m)
            out.extend(_all_contained(m))
    return out


def derives_by_select(s1: Stage, s2: Stage) -> bool:
    """D14(iii), derive-by-Select: for some A in LA_i, S_i+1 = Select(A, S_i)."""
    return any(select(li, s1) == s2 for li in s1.la)


def derives_by_merge(s1: Stage, s2: Stage, merge_rule: Callable = None) -> bool:
    """D14(iii), derive-by-Merge: LA_i = LA_i+1 and for some A, B
      (a) A is in W_i,
      (b) either A contains B or W_i immediately contains B, and
      (c) W_i+1 = (W_i - {A,B}) u {Merge(A,B)}.

    The first disjunct of (b) is internal Merge, the second external Merge.
    `merge_rule` is Triggered Merge (D27, which replaces D13) by default.
    """
    rule = merge_rule or triggered_merge
    if s1.la != s2.la:
        return False
    for A in s1.w:
        for B in set(s1.w) | set(_all_contained(A)):
            try:
                m = rule(A, B)
            except ValueError:
                continue
            if s2.w == (s1.w - {A, B}) | {m}:
                return True
    return False


def apply_merge(s: Stage, A: SO, B: SO, merge_rule: Any = None) -> Stage:
    """The stage that derive-by-Merge (D14) produces from S with A and B."""
    if A not in s.w:
        raise ValueError(f"Merge undefined here: {A!r} is not a root of the workspace (D11, D14a)")
    if not (B in s.w or contains(A, B)):
        raise ValueError(
            f"Merge undefined here: {B!r} is neither a root nor contained in {A!r} (D14b)")
    m = (merge_rule or triggered_merge)(A, B)
    return Stage(s.la, (s.w - {A, B}) | {m})


def is_internal_merge(A: SO, B: SO) -> bool:
    """The internal-Merge disjunct of D14(b): A contains B."""
    return contains(A, B)


def derives(s1: Stage, s2: Stage, merge_rule: Callable = None) -> bool:
    """One clause of D14(iii) / D38(iii): S_i+1 follows from S_i by Select, by
    Merge, or (D38) by Transfer."""
    return (derives_by_merge(s1, s2, merge_rule) or derives_by_select(s1, s2)
            or derives_by_transfer(s1, s2))


def is_derivation(stages: Sequence[Stage], lex: Lexicon,
                  merge_rule: Callable = None) -> bool:
    """D14, extended by D38.  A derivation from lexicon L is a finite sequence
    of stages <S1,...,Sn>, n >= 1, such that
      (i)   every LI with <LI,k> in LA_1 is in L,
      (ii)  W_1 = {}, and
      (iii) each S_i+1 follows from S_i by Select, Merge or Transfer.

    Note that, unlike the 2011 draft, D14 does not require LA_n = {} or a
    single root; that is D15.
    """
    if not stages:
        return False
    if any(t.li not in lex for t in stages[0].la):
        return False
    if stages[0].w != frozenset():
        return False
    return all(derives(stages[i], stages[i + 1], merge_rule)
               for i in range(len(stages) - 1))


def derived_object(stages: Sequence[Stage], lex: Lexicon,
                   merge_rule: Callable = None) -> Optional[Any]:
    """D15. A is derivable from L iff there is a derivation whose last stage
    has LA_n = {} and W_n = {A}.  Returns that A, or None."""
    if not is_derivation(stages, lex, merge_rule):
        return None
    last = stages[-1]
    if last.la or len(last.w) != 1:
        return None
    return next(iter(last.w))


# =====================================================================
# 4. Occurrences  (D16-D22, T1-T3)
# =====================================================================

Path = Tuple[SO, ...]


def positions(A: SO, B: SO) -> List[Path]:
    """D16/D17. Every position (path <B,...,A>) at which A occurs in B.

    A path is a sequence <SO1,...,SOn> with SO_i+1 a member of SO_i.  The
    recursion does not descend into Transferred pairs.
    """
    out: List[Path] = []

    def walk(cur: SO, path: Path) -> None:
        if cur == A:
            out.append(path)
        if isinstance(cur, frozenset):
            for m in cur:
                if isinstance(m, Transferred):
                    continue
                walk(m, path + (m,))

    walk(B, (B,))
    return out


def occurs_in(B: SO, A: SO) -> bool:
    """D17. B occurs in A at some position P = <A,...,B>."""
    return len(positions(B, A)) > 0


def occ_immediately_contains(p: Path, q: Path) -> bool:
    """D18. Occurrence B_P immediately contains occurrence A_P' iff
    P = <X1,...,Xn> and P' = <X1,...,Xn,Xn+1>."""
    return len(q) == len(p) + 1 and q[:len(p)] == p


def occ_contains(p: Path, q: Path) -> bool:
    """Transitive closure of D18: P is a proper prefix of P'."""
    return len(q) > len(p) and q[:len(p)] == p


def are_sisters(A: SO, B: SO, C: SO) -> bool:
    """D19. A and B (A != B) are sisters in C iff A, B are members of C."""
    return A != B and isinstance(C, frozenset) and A in C and B in C


def sister_positions(p: Path) -> List[Path]:
    """D20. A_P is a sister of B_P' iff P and P' agree except at the last
    step.  Returns every such P'."""
    if len(p) < 2:
        return []
    parent = p[-2]
    return [p[:-1] + (m,) for m in parent
            if m != p[-1] and not isinstance(m, Transferred)]


def c_commands(A: SO, B: SO, D: SO) -> bool:
    """D21. A c-commands B in D iff some sister C of A in D is B or contains B."""
    for p in positions(A, D):
        for sp in sister_positions(p):
            C = sp[-1]
            if C == B or contains(C, B):
                return True
    return False


def asymmetrically_c_commands(A: SO, B: SO, D: SO) -> bool:
    """D21, second clause: A c-commands B and A and B are not sisters."""
    if not c_commands(A, B, D):
        return False
    sisters = any(are_sisters(A, B, p[-1]) for p in positions_of_sets(D))
    return not sisters


def positions_of_sets(D: SO) -> List[Path]:
    """Every occurrence of a set in D (including D itself)."""
    return [p for p in all_paths(D) if isinstance(p[-1], frozenset)]


def occ_c_commands(p: Path, q: Path) -> bool:
    """D22. In D, A_P c-commands B_P' iff there is an occurrence C_P'' that is
    a sister of A_P and either is B_P' or contains B_P'."""
    for sp in sister_positions(p):
        if sp == q or occ_contains(sp, q):
            return True
    return False


def theorem1_holds(D: SO) -> bool:
    """T1. Occurrence-level immediate containment implies object-level
    immediate containment, and every occurrence of B immediately contains an
    occurrence of each A in B."""
    paths = all_paths(D)
    for p in paths:
        for q in paths:
            if occ_immediately_contains(p, q) and not immediately_contains(p[-1], q[-1]):
                return False
    for p in paths:
        B = p[-1]
        if isinstance(B, frozenset):
            for A in B:
                if not isinstance(A, Transferred) and p + (A,) not in paths:
                    return False
    return True


def theorem2_holds(D: SO) -> bool:
    """T2. If in D, A_P is a sister of B_P', then A and B are sisters in some C."""
    for p in all_paths(D):
        for sp in sister_positions(p):
            if not are_sisters(p[-1], sp[-1], p[-2]):
                return False
    return True


def theorem3_holds(D: SO) -> bool:
    """T3. If in D, A_P c-commands B_P', then A c-commands B in D."""
    paths = all_paths(D)
    for p in paths:
        for q in paths:
            if occ_c_commands(p, q) and not c_commands(p[-1], q[-1], D):
                return False
    return True


def all_paths(A: SO, prefix: Path = ()) -> List[Path]:
    """Every path starting at A: A itself and every occurrence in it."""
    out: List[Path] = []

    def walk(cur: SO, pth: Path) -> None:
        out.append(pth)
        if isinstance(cur, frozenset):
            for m in cur:
                if not isinstance(m, Transferred):
                    walk(m, pth + (m,))

    walk(A, prefix + (A,))
    return out


# =====================================================================
# 5. Digression: syntactic objects built from chains  (D16', D7', D13',
#    D14', D15', T4)
# =====================================================================
#
# Section 5 compares the token-based system with one that has no indices and
# instead marks each internally merged set with a path (a "chain link").  A
# Chain-based syntactic object is a pair <S, P>.  Lexical items appear without
# tokens, so there are no lexical arrays, workspaces or Select.

@dataclass(frozen=True)
class ChainSO:
    """D7'. A pair <S, P> is a (Chain-based) syntactic object iff S is a lexical
    item, or a set of Chain-based syntactic objects, and P is a path (D16')."""
    s: Any                                   # LexicalItem | frozenset[ChainSO]
    p: Tuple["ChainSO", ...] = ()            # () is the trivial path e

    def __repr__(self) -> str:
        if isinstance(self.s, LexicalItem):
            core = repr(self.s)
        else:
            core = "{" + ", ".join(sorted(repr(m) for m in self.s)) + "}"
        if self.p:
            core += "<" + ", ".join(_chain_brief(x) for x in self.p) + ">"
        return core


def _chain_brief(x: ChainSO) -> str:
    return repr(x.s) if isinstance(x.s, LexicalItem) else "{..}" if len(repr(x)) > 30 else repr(x)


def chain_positions(B: ChainSO, A: ChainSO) -> List[Tuple[ChainSO, ...]]:
    """D16'. Every path <<S1,P1>,...,<Sn,Pn>> from A to B with S_i+1 in S_i."""
    out: List[Tuple[ChainSO, ...]] = []

    def walk(cur: ChainSO, path: Tuple[ChainSO, ...]) -> None:
        if cur == B:
            out.append(path)
        if isinstance(cur.s, frozenset):
            for m in cur.s:
                walk(m, path + (m,))

    walk(A, (A,))
    return out


def chain_merge(A: ChainSO, B: ChainSO, p: Tuple[ChainSO, ...] = ()) -> ChainSO:
    """D13'. Given distinct Chain-based syntactic objects A, B, Merge(A,B) =
    {A,B}; D14'(ii) pairs the result with a path P."""
    if A == B:
        raise ValueError("Merge undefined: A and B are not distinct (D13')")
    return ChainSO(frozenset({A, B}), p)


def chain_locality_ok(B: ChainSO, path: Tuple[ChainSO, ...]) -> bool:
    """D14'(ii)(c), the locality condition, read as: no node on the path above
    B's mother has B as a member, i.e. the path does not pass by a higher
    (c-commanding) occurrence of B on its way to a lower one.

    As printed, (c) quantifies over every i < k, which includes B's own mother
    and would block every internal Merge, (7') included; we read it as
    i < k-1.                                                      # STIPULATION
    """
    return all(B not in node.s for node in path[:-2] if isinstance(node.s, frozenset))


def is_chain_derivation(seq: Sequence[ChainSO], lex: Iterable[LexicalItem]) -> bool:
    """D14'. A Chain-based derivation from L is a finite sequence <S'1,...,S'n>
    where each S'_i = <S_i, P_i> is either
      (i)  a lexical item of L with P_i = e, or
      (ii) S_i = Merge(A,B) = {A,B} where
           (a) A and B appear earlier in the derivation,
           (b) either P_i is a position of B in A (internal) or P_i = e
               (external), and
           (c) the locality condition (see chain_locality_ok).
    """
    lex = set(lex)
    for i, x in enumerate(seq):
        if isinstance(x.s, LexicalItem):
            if x.s not in lex or x.p != ():
                return False
            continue
        if not isinstance(x.s, frozenset) or len(x.s) != 2:
            return False
        earlier = set(seq[:i])
        ok = False
        for A, B in itertools.permutations(x.s, 2):
            if A not in earlier or B not in earlier:
                continue
            if x.p == ():
                ok = True
            elif x.p in chain_positions(B, A) and chain_locality_ok(B, x.p):
                ok = True
        if not ok:
            return False
    return bool(seq)


def chain_derivable(A: ChainSO, seq: Sequence[ChainSO], lex: Iterable[LexicalItem]) -> bool:
    """D15'. A is derivable from L iff some Chain-based derivation ends in A."""
    return bool(seq) and seq[-1] == A and is_chain_derivation(seq, lex)


# -- Theorem 4, checked on bounded fragments ------------------------------
#
# T4: let T(Lex) be the token-based objects with derivations in which Merge
# never applies to two objects one of which is a renumbering of the other,
# [T(Lex)] its classes under renumbering, and C(Lex) the Chain-based
# derivable objects.  There is a one-to-one, onto, structure-preserving
# correspondence between [T(Lex)] and C(Lex).
#
# Both sets are infinite, so we compare them up to a size bound.  The size of
# an object is the number of set nodes in its tree unfolding (a moved phrase
# counts at each of its positions), which the correspondence preserves.

def unfolded_size(X: Any) -> int:
    if isinstance(X, ChainSO):
        X = X.s
    if isinstance(X, frozenset):
        return 1 + sum(unfolded_size(m) for m in X)
    return 0


def _tokens_in(X: SO) -> Set[LIToken]:
    if isinstance(X, LIToken):
        return {X}
    out: Set[LIToken] = set()
    for m in X:
        out |= _tokens_in(m)
    return out


def _renumber(X: SO, f: Dict[LIToken, LIToken]) -> SO:
    if isinstance(X, LIToken):
        return f[X]
    return frozenset(_renumber(m, f) for m in X)


def renumbering_class(X: SO) -> SO:
    """A canonical representative of X's class under renumbering (bijective
    re-indexing of tokens of the same lexical item)."""
    toks = sorted(_tokens_in(X), key=lambda t: (t.li.name, t.k))
    by_li: Dict[LexicalItem, List[LIToken]] = {}
    for t in toks:
        by_li.setdefault(t.li, []).append(t)
    groups = sorted(by_li.items(), key=lambda kv: kv[0].name)
    best, best_key = None, None
    for perms in itertools.product(*(itertools.permutations(ts) for _, ts in groups)):
        f: Dict[LIToken, LIToken] = {}
        n = 1
        for (li, _), perm in zip(groups, perms):
            for t in perm:
                f[t] = LIToken(li, n)
                n += 1
        Y = _renumber(X, f)
        key = _canon_str(Y)
        if best_key is None or key < best_key:
            best, best_key = Y, key
    return best


def _canon_str(X: SO) -> str:
    if isinstance(X, LIToken):
        return f"{X.li.name}{X.k}"
    return "{" + ",".join(sorted(_canon_str(m) for m in X)) + "}"


def is_renumbering(A: SO, B: SO) -> bool:
    return renumbering_class(A) == renumbering_class(B)


@lru_cache(maxsize=None)
def _token_to_chain(X: SO, locality: bool) -> Tuple[ChainSO, ...]:
    if isinstance(X, LIToken):
        return (ChainSO(X.li),)
    a, b = tuple(X)
    internal = contains(a, b) or contains(b, a)
    big, small = (a, b) if contains(a, b) else (b, a)
    out: List[ChainSO] = []
    for cbig in _token_to_chain(big, locality):
        for csmall in _token_to_chain(small, locality):
            if cbig == csmall:
                continue
            if not internal:
                out.append(ChainSO(frozenset({cbig, csmall})))
                continue
            # translate each token position of `small` in `big`, node by node
            for tp in positions(small, big):
                cp, cur = [cbig], cbig
                for t in tp[1:]:
                    imgs = set(_token_to_chain(t, locality))
                    nxt = [m for m in cur.s if m in imgs]
                    if len(nxt) != 1:
                        break
                    cur = nxt[0]
                    cp.append(cur)
                else:
                    cp_t = tuple(cp)
                    if cur == csmall and (not locality or chain_locality_ok(csmall, cp_t)):
                        out.append(ChainSO(frozenset({cbig, csmall}), cp_t))
    return tuple(dict.fromkeys(out))


def token_to_chain(X: SO, locality: bool = True) -> List[ChainSO]:
    """The Chain-based objects that correspond to the token-based X.

    Tokens lose their index.  A set {A,B} where B is contained in A was built
    by internal Merge (by T6 it cannot have been external), and is indexed
    with the image of a token position of B in A -- one that satisfies the
    locality condition D14'(c) when `locality` is set.  A list is returned:
    T4 needs it to have exactly one member.
    """
    return list(_token_to_chain(X, locality))


def token_classes_up_to(items: Sequence[LexicalItem], k: int) -> Set[SO]:
    """[T(Lex)] restricted to objects of unfolded size <= k.

    An object is derivable (D15) iff it is a token, or {A,B} with A, B
    derivable and token-disjoint (external Merge, both roots of one
    workspace), or {A,B} with B contained in A (internal Merge).  Merges of
    renumberings are excluded, as T4 requires."""
    classes: Set[SO] = {LIToken(li, 1) for li in items}
    for size in range(1, k + 1):
        new: Set[SO] = set()
        cur = list(classes)
        for A in cur:
            for B in cur:
                if unfolded_size(A) + unfolded_size(B) + 1 == size:
                    if is_renumbering(A, B):
                        continue
                    shift = max(t.k for t in _tokens_in(A))
                    B2 = _renumber(B, {t: LIToken(t.li, t.k + shift) for t in _tokens_in(B)})
                    new.add(renumbering_class(frozenset({A, B2})))
            if isinstance(A, frozenset):
                for B in set(_all_contained(A)):
                    if unfolded_size(A) + unfolded_size(B) + 1 == size:
                        new.add(renumbering_class(frozenset({A, B})))
        classes |= new
    return classes


def chain_objects_up_to(items: Sequence[LexicalItem], k: int,
                        locality: bool = True) -> Set[ChainSO]:
    """C(Lex) restricted to objects of unfolded size <= k (D14', D15')."""
    objs: Set[ChainSO] = {ChainSO(li) for li in items}
    for size in range(1, k + 1):
        new: Set[ChainSO] = set()
        cur = list(objs)
        for A in cur:
            for B in cur:
                if A == B or unfolded_size(A) + unfolded_size(B) + 1 != size:
                    continue
                new.add(chain_merge(A, B))
                for p in chain_positions(B, A):
                    if not locality or chain_locality_ok(B, p):
                        new.add(chain_merge(A, B, p))
        objs |= new
    return objs


def theorem4_report(items: Sequence[LexicalItem], k: int,
                    locality: bool = True) -> Dict[str, Any]:
    """Compare [T(Lex)] and C(Lex) up to size k under `token_to_chain`.

    `locality=False` drops D14'(c) on both sides."""
    T = token_classes_up_to(items, k)
    C = chain_objects_up_to(items, k, locality)
    image: Dict[ChainSO, List[SO]] = {}
    not_one = []
    for X in T:
        cs = token_to_chain(X, locality)
        if len(cs) != 1:
            not_one.append((X, cs))
        for c in cs:
            image.setdefault(c, []).append(X)
    many_to_one = {c: xs for c, xs in image.items() if len(xs) > 1}
    missing = C - set(image)
    return {
        "token classes": len(T), "chain objects": len(C),
        "token objects without a unique chain image": not_one,
        "chain objects hit twice": many_to_one,
        "chain objects with no token preimage": missing,
        "bijection": not not_one and not many_to_one and not missing,
    }


# =====================================================================
# 6. General properties of derivations  (D23, D24, T5-T11)
# =====================================================================

def is_derivable_workspace(W: FrozenSet[SO], stages: Sequence[Stage],
                           lex: Lexicon) -> bool:
    """D23. W is derivable iff it is W_n of some derivation from some lexicon;
    here: of the given derivation.  (A syntactic object is derivable iff it is
    derivable, D15, from some lexicon.)"""
    return is_derivation(stages, lex) and stages[-1].w == W


def is_binary_branching(A: SO) -> bool:
    """D24 / Theorem 5. A is binary branching iff A and everything contained in
    A is a lexical item token or immediately contains exactly two objects."""
    if isinstance(A, (LIToken, Transferred)):
        return True
    if not isinstance(A, frozenset):
        return False
    return len(A) == 2 and all(is_binary_branching(m) for m in A)


def unique_root_occurrences(w: FrozenSet[SO]) -> bool:
    """Theorem 6. If A is a root in a derivable W, there is no other root B in
    W such that A contains an occurrence of B."""
    return not any(A != B and contains(A, B) for A in w for B in w)


def _contained_in_workspace(w: FrozenSet[SO]) -> Set[SO]:
    out: Set[SO] = set(w)
    for X in w:
        out |= set(_all_contained(X))
    return out


def satisfies_ntc(s1: Stage, s2: Stage) -> bool:
    """Theorem 8 (No Tampering Condition). For consecutive stages, every A
    contained in W1 is contained in W2."""
    after = _contained_in_workspace(s2.w)
    return _contained_in_workspace(s1.w) <= after


def satisfies_extension(s1: Stage, s2: Stage) -> bool:
    """Theorem 9 (Extension Condition). If S1 derives S2 by Merge, some A in W1
    and C in W2 have (i) C not in W1, (ii) A not in W2, (iii) A in C in W2."""
    return any(C not in s1.w and isinstance(C, frozenset)
               and any(A not in s2.w and A in C for A in s1.w)
               for C in s2.w)


def satisfies_inclusiveness(stages: Sequence[Stage]) -> bool:
    """Theorem 10 (Inclusiveness). The only elements contained in W_n are the
    lexical item tokens of LA_1 and syntactic objects containing them (and,
    once Transfer has applied, the interface pairs it produced)."""
    la1 = stages[0].la
    ok = True

    def walk(X: SO) -> None:
        nonlocal ok
        if isinstance(X, LIToken):
            ok = ok and X in la1
        elif isinstance(X, frozenset):
            for m in X:
                walk(m)
        elif isinstance(X, Transferred):
            pass
        else:
            ok = False

    for X in stages[-1].w:
        walk(X)
    return ok


def two_occurrences_iff_internal_merge(stages: Sequence[Stage],
                                       ops: Sequence[str]) -> bool:
    """Theorem 7. A derivable workspace contains two occurrences of A iff A or
    some B containing A has undergone internal Merge.  `ops[i]` names the
    operation that produced stages[i]."""
    w = stages[-1].w
    moved = any(op == "internal Merge" for op in ops)
    multi = any(len(positions(o, r)) > 1 for r in w for o in set(_all_contained(r)))
    return moved == multi


# Theorem 11 (Local Economy): whether an operation applies to the elements of
# W_i is determined by W_i alone.  In this implementation it holds by
# construction: `derives` and every operation are functions of the current
# stage and nothing else; there is no other state to consult.


# =====================================================================
# 7. Labels  (D25-D33, T12, T13)
# =====================================================================

def trigger_features(li: LIToken) -> Tuple[Feature, ...]:
    """D25. The trigger features of a lexical item token, ranked."""
    return tuple(sorted((f for f in li.li.syn if f.trigger),
                        key=lambda f: (f.order, f.name)))


def _lowest_rank(tfs: Tuple[Feature, ...], C: SO) -> Feature:
    return tfs[0]


# Which trigger feature D26(ii) checks.  The paper: Triggers is "a class of
# functions"; when Triggers(B) has more than one element, Triggers({B,C})
# "will check a particular one, determined by B and C, and we leave aside the
# question of which one it is"; and it explicitly does *not* assume trigger
# features are ordered.  Derivability under D27 depends only on how many
# trigger features remain, never on which, so for the axioms proper any
# choice gives the same derivations.  The default discharges the lowest-ranked
# feature; `extensions.py` swaps in a choice determined by C.   # STIPULATION
DISCHARGE: Callable[[Tuple[Feature, ...], SO], Feature] = _lowest_rank


def triggers(A: SO) -> Tuple[Feature, ...]:
    """D26. Triggers maps each syntactic object A to a subset of its trigger
    features:
      (i)   if A is a lexical item token, all of its trigger features;
      (ii)  if A = {B,C} with Triggers(B) non-empty and Triggers(C) = {},
            Triggers(B) - {TF} for some TF in Triggers(B);
      (iii) otherwise undefined.
    """
    if isinstance(A, LIToken):
        return trigger_features(A)
    if isinstance(A, Transferred):
        return ()                      # see D36: the pair stands for a complement
    if not isinstance(A, frozenset) or len(A) != 2:
        raise ValueError(f"Triggers undefined for {A!r} (D26iii)")
    nonempty = [m for m in A if triggers(m)]
    if len(nonempty) != 1:
        raise ValueError(f"Triggers undefined for {A!r}: {len(nonempty)} members "
                         "have trigger features (D26iii)")
    B = nonempty[0]
    (C,) = [m for m in A if m != B]
    rest = triggers(B)
    tf = DISCHARGE(rest, C)
    return tuple(f for f in rest if f != tf)


def projector(A: FrozenSet[SO]) -> Tuple[SO, SO]:
    """For A = {X,Y}, return (the member with non-empty Triggers, the other).

    By D27 exactly one member of a Merge output has non-empty Triggers, and by
    D28 / Theorem 13 that is the one whose label projects.
    """
    members = list(A)
    if len(members) != 2:
        raise ValueError(f"{A!r} is not binary")
    a, b = members
    ta, tb = triggers(a), triggers(b)
    if bool(ta) == bool(tb):
        raise ValueError(f"{A!r} is not a triggered-Merge output")
    return (a, b) if ta else (b, a)


def label(A: SO) -> LIToken:
    """D28. Label maps syntactic objects to lexical item tokens:
      (i)  Label(LI) = LI;
      (ii) if {A,B} is contained in a derivable W and Triggers(A) is
           non-empty, Label({A,B}) = Label(A).
    Theorem 13 is immediate: if C = Merge(A,B) then Label(C) = Label(A).
    """
    if isinstance(A, LIToken):
        return A
    head, _ = projector(A)
    return label(head)


def is_maximal_projection(C: SO, root: SO) -> bool:
    """D29. C is a maximal projection of LI (Max_W(LI)) iff Label(C) = LI and no
    D contained in W immediately containing C has Label(D) = Label(C)."""
    lab = label(C)
    for p in positions(C, root):
        if len(p) >= 2 and label(p[-2]) == lab:
            return False
    return True


def is_minimal_projection(C: SO) -> bool:
    """D30. C is a minimal projection iff C is a lexical item token."""
    return isinstance(C, LIToken)


def is_intermediate_projection(C: SO, root: SO) -> bool:
    """D31. Neither minimal nor maximal."""
    return not is_minimal_projection(C) and not is_maximal_projection(C, root)


def complement_of(X: SO, C: SO) -> Optional[SO]:
    """D32. Y is the complement of X in C iff C = Merge(X,Y) and X is a lexical
    item token."""
    if not isinstance(C, frozenset) or len(C) != 2:
        return None
    head, other = projector(C)
    if head == X and isinstance(X, LIToken):
        return other
    return None


def specifier_of(X: SO, C: SO) -> Optional[SO]:
    """D33. Y is the specifier of X in C iff C = Merge(X,Y) and X is not a
    lexical item token (we then also say Y is a specifier of Label(X), and
    Y = Spec XP for XP the maximal projection of that label)."""
    if not isinstance(C, frozenset) or len(C) != 2:
        return None
    head, other = projector(C)
    if head == X and not isinstance(X, LIToken):
        return other
    return None


# =====================================================================
# 8. Transfer  (D34-D38, T14)
# =====================================================================

PHASE_CATEGORIES = ("Comp", "v*")


def is_strong_phase(so: SO, root: Optional[SO] = None) -> bool:
    """D35. SO is a strong phase iff SO is a maximal projection with label LI
    and the category of LI is Comp, or transitive or unergative v (written v*).

    Maximality (D29) is relative to the workspace; `root` is the root that
    contains SO (default: SO is itself a root, hence maximal).
    """
    if not isinstance(so, frozenset):
        return False
    try:
        h = label(so)
        if root is not None and not is_maximal_projection(so, root):
            return False
    except ValueError:
        return False
    return any(f.name in PHASE_CATEGORIES for f in h.li.syn if not f.trigger)


def transfer(P: SO, so: SO) -> Transferred:
    """D34. For SO with Triggers(SO) = {}, Transfer(P,SO) =
    <TransferPF(P,SO), TransferLF(P,SO)>, relativized to the phase P."""
    if triggers(so):
        raise ValueError(f"Transfer undefined: Triggers({so!r}) is non-empty (D34)")
    return Transferred(transfer_pf(P, so), transfer_lf(P, so))


def phase_complement_path(so: SO) -> Path:
    """The position of the complement (D32) of the label of the phase."""
    h = label(so)
    for p in positions(h, so):
        if len(p) >= 2:
            comp = complement_of(h, p[-2])
            if comp is not None:
                return p[:-1] + (comp,)
    raise ValueError(f"no complement of the phase head in {so!r}")


def replace_at(path: Path, new: Any) -> SO:
    """Rebuild the root of `path` with the object at the end of `path`
    replaced by `new` (only at that position)."""
    if len(path) == 1:
        return new
    parent = path[-2]
    rebuilt = frozenset([new] + [m for m in parent if m != path[-1]])
    return replace_at(path[:-1], rebuilt)


def cyclic_transfer(so: SO) -> SO:
    """D36. For a derivable W with SO in W a strong phase and A the complement
    of the label of the phase, Cyclic-Transfer(SO) = SO', obtained from SO by
    replacing A by <TransferPF(SO,A), TransferLF(SO,A)>.

    "Replacing A" is read positionally: the occurrence of A that is the
    complement is replaced.  (A phase-head complement with a second
    occurrence never arises in the derivations here.)
    """
    if not is_strong_phase(so):
        raise ValueError(f"Cyclic-Transfer undefined: {so!r} is not a strong phase (D35)")
    path = phase_complement_path(so)
    A = path[-1]
    if isinstance(A, Transferred):
        raise ValueError("Cyclic-Transfer undefined: the complement is already transferred")
    return replace_at(path, transfer(so, A))


def untransferred_inner_phases(so: SO) -> List[SO]:
    """D38's side condition: the strong phases properly contained in SO whose
    complement has not yet been transferred."""
    out = []
    for X in set(_all_contained(so)):
        if is_strong_phase(X, root=so):
            try:
                comp = phase_complement_path(X)[-1]
            except ValueError:
                continue
            if not isinstance(comp, Transferred):
                out.append(X)
    return out


def derives_by_transfer(s1: Stage, s2: Stage) -> bool:
    """D38(iii), derive-by-Transfer: SO in W_i is a strong phase containing no
    other strong phase whose complement has not yet been transferred, and
      (a) W_i+1 = (W_i - {SO}) u {Transfer(SO,SO)}   (ends the derivation), or
      (b) W_i+1 = (W_i - {SO}) u {Cyclic-Transfer(SO)}.

    D38 does not say what LA_i+1 is in this clause; we require it to equal
    LA_i, as for Merge.                                           # STIPULATION
    """
    if s1.la != s2.la:
        return False
    for so in s1.w:
        if not is_strong_phase(so) or untransferred_inner_phases(so):
            continue
        rest = s1.w - {so}
        try:
            if s2.w == rest | {transfer(so, so)}:
                return True
        except ValueError:
            pass
        try:
            if s2.w == rest | {cyclic_transfer(so)}:
                return True
        except ValueError:
            pass
    return False


def pic_blocks(alpha_after: SO, target: SO) -> bool:
    """Theorem 14 (PIC). In Cyclic-Transfer(alpha) = {...{H,Z}...}, Merge cannot
    apply to Z or anything contained in Z: Z is a Transferred pair, not a
    syntactic object, and contains none.  So an object that occurred only
    inside the complement is no longer contained in the phase."""
    return not contains(alpha_after, target)


# =====================================================================
# 9. TransferLF  (D39)
# =====================================================================

def transfer_lf(phase: SO, so: SO) -> Any:
    """D39. For Phase in a derivable W with a strong-phase label, and SO equal
    to or contained in Phase:
      (a) TransferLF(Phase, <<Sem,Syn,Phon>,k>) = <Sem,k>
      (b) TransferLF(Phase, {X,Y}) = {TransferLF(Phase,X), TransferLF(Phase,Y)}
      (c) TransferLF(Phase, <PHON,SEM>) = SEM
    None of the clauses consults Phase in this preliminary version.
    """
    if isinstance(so, LIToken):
        return LFObject(so.li.sem, so.k)
    if isinstance(so, Transferred):
        return so.lf
    return frozenset(transfer_lf(phase, m) for m in so)


# =====================================================================
# 10. TransferPF  (D40, D41)
# =====================================================================

@lru_cache(maxsize=None)
def _subobjects(so: SO) -> FrozenSet[SO]:
    """SO and every set contained in it."""
    out = {so} if isinstance(so, frozenset) else set()
    if isinstance(so, frozenset):
        for m in so:
            if isinstance(m, frozenset):
                out |= _subobjects(m)
    return frozenset(out)


@lru_cache(maxsize=None)
def is_final(A: SO, AB: SO, so: SO) -> bool:
    """D40. A in {A,B} is final in SO iff there is no C contained in (or equal
    to) SO such that A is in C and C contains {A,B}.  Otherwise A is non-final
    in SO.

    Finality is a property of the pair (A, {A,B}), not of an occurrence: if
    {A,B} has several occurrences, A is final in all of them or in none.
    """
    return not any(A in C and contains(C, AB) for C in _subobjects(so))


def is_nonfinal_occurrence(p: Path, so: SO) -> bool:
    """Convenience: the occurrence at path p (in SO = p[0]'s tree) is the
    member p[-1] of the set p[-2]; it is non-final iff D40 says so."""
    return len(p) >= 2 and not is_final(p[-1], p[-2], so)


def transfer_pf(phase: SO, so: SO) -> Tuple[Feature, ...]:
    """D41. For Phase in a derivable W with a strong-phase label, and SO equal
    to or contained in Phase:
      (a) a lexical item token <<Sem,Syn,Phon>,k>  ->  Phon
      (b) {X,Y}, X and Y final in Phase  ->  PF(X)^PF(Y), if Y is the
          complement of X or X is the specifier of Y
      (c) {X,Y}, X final in Phase but Y not  ->  PF(X)
      (d) {X,Y}, both non-final in Phase  ->  the empty sequence
      (e) <PHON,SEM>  ->  PHON
    Clause (b) makes Specifier-Head-Complement the only order.
    """
    if isinstance(so, Transferred):
        return so.pf                                            # (e)
    if isinstance(so, LIToken):
        return so.li.phon                                       # (a)
    head, other = projector(so)
    # X precedes Y: head ^ complement, or specifier ^ head
    X, Y = (head, other) if isinstance(head, LIToken) else (other, head)
    fx, fy = is_final(X, so, phase), is_final(Y, so, phase)
    if fx and fy:
        return transfer_pf(phase, X) + transfer_pf(phase, Y)    # (b)
    if fx:
        return transfer_pf(phase, X)                            # (c)
    if fy:
        return transfer_pf(phase, Y)                            # (c)
    return ()                                                   # (d)


# =====================================================================
# 12. NTC-respecting TransferPF
# =====================================================================
#
# Section 12 sketches an alternative in which Cyclic-Transfer leaves syntactic
# objects untouched.  Transfer becomes "the establishment of an association
# between objects in the workspace and interface outputs ... a pair of
# functions LF, PF" that start empty and are extended as the derivation
# proceeds; "the list of already transferred elements is given exactly by the
# domains of these functions", and "the accessible parts of workspace W are
# given by W minus those already transferred".  The formal version is in an
# appendix that is not part of the published paper, so the details below are
# this implementation's.
#
# Two readings of "W minus those already transferred" are possible, and they
# come apart as soon as anything moves out of a phase:
#   "occurrence": an occurrence is inaccessible iff its path passes through a
#                 transferred object (an object that also sits at a phase
#                 edge stays accessible there);
#   "object":     an object is inaccessible iff it is, or is contained in, a
#                 transferred object.                             # STIPULATION

@dataclass(frozen=True)
class NTCStage:
    """D10 as section 12 needs it: <LA, W, PF, LF>, with PF and LF finite
    functions (stored as tuples of argument-value pairs)."""
    la: FrozenSet[LIToken]
    w: FrozenSet[SO]
    pf: Tuple[Tuple[SO, Tuple[Feature, ...]], ...] = ()
    lf: Tuple[Tuple[SO, Any], ...] = ()

    def domain(self) -> FrozenSet[SO]:
        return frozenset(a for a, _ in self.pf)


def is_accessible(p: Path, dom: FrozenSet[SO], reading: str = "occurrence") -> bool:
    """Is the occurrence at path p in the accessible part of the workspace?"""
    if reading == "occurrence":
        return not any(x in dom for x in p[1:])
    X = p[-1]
    return X not in dom and not any(contains(T, X) for T in dom)


def transfer_pf_ntc(phase: SO, so: SO, pf: Dict[SO, Tuple[Feature, ...]]) -> Tuple[Feature, ...]:
    """D41 restated for section 12: an object already in the domain of PF
    contributes its stored value (this replaces clause (e)); finality (D40) is
    computed on the intact phase."""
    if so in pf:
        return pf[so]
    if isinstance(so, LIToken):
        return so.li.phon
    head, other = projector(so)
    X, Y = (head, other) if isinstance(head, LIToken) else (other, head)
    fx, fy = is_final(X, so, phase), is_final(Y, so, phase)
    out: Tuple[Feature, ...] = ()
    if fx:
        out += transfer_pf_ntc(phase, X, pf)
    if fy:
        out += transfer_pf_ntc(phase, Y, pf)
    return out


def transfer_lf_ntc(phase: SO, so: SO, lf: Dict[SO, Any]) -> Any:
    """D39 restated for section 12 (clause (c) becomes a lookup in LF)."""
    if so in lf:
        return lf[so]
    if isinstance(so, LIToken):
        return LFObject(so.li.sem, so.k)
    return frozenset(transfer_lf_ntc(phase, m, lf) for m in so)


def untransferred_inner_phases_ntc(so: SO, dom: FrozenSet[SO]) -> List[SO]:
    """D38's side condition, with "transferred" meaning "in the domain of PF"."""
    out = []
    for X in set(_all_contained(so)):
        if is_strong_phase(X, root=so):
            try:
                comp = phase_complement_path(X)[-1]
            except ValueError:
                continue
            if comp not in dom:
                out.append(X)
    return out


def cyclic_transfer_ntc(s: NTCStage, so: SO) -> NTCStage:
    """D36 under section 12: extend PF and LF with the complement A of the
    phase label, leaving W exactly as Merge built it."""
    if so not in s.w or not is_strong_phase(so):
        raise ValueError(f"Cyclic-Transfer undefined: {so!r} is not a strong phase in W (D35)")
    if untransferred_inner_phases_ntc(so, s.domain()):
        raise ValueError("Transfer undefined: contains a strong phase whose "
                         "complement has not been transferred (D38)")
    A = phase_complement_path(so)[-1]
    if A in s.domain():
        raise ValueError("Cyclic-Transfer undefined: the complement is already transferred")
    pf, lf = dict(s.pf), dict(s.lf)
    return NTCStage(s.la, s.w,
                    s.pf + ((A, transfer_pf_ntc(so, A, pf)),),
                    s.lf + ((A, transfer_lf_ntc(so, A, lf)),))


def transfer_ntc(s: NTCStage, so: SO) -> Transferred:
    """Transfer(SO,SO) (D34, D38a) under section 12: the interface pair is
    handed to SM and CI, and the workspace is left as Merge built it."""
    if triggers(so):
        raise ValueError(f"Transfer undefined: Triggers({so!r}) is non-empty (D34)")
    if untransferred_inner_phases_ntc(so, s.domain()):
        raise ValueError("Transfer undefined: contains a strong phase whose "
                         "complement has not been transferred (D38)")
    return Transferred(transfer_pf_ntc(so, so, dict(s.pf)),
                       transfer_lf_ntc(so, so, dict(s.lf)))


# =====================================================================
# 13. Convergence  (D42-D44)
# =====================================================================

def _features_of(x: Any, kind: str) -> List[Feature]:
    out: List[Feature] = []
    if isinstance(x, LFObject):
        out.extend(f for f in x.sem if f.kind == kind)
    elif isinstance(x, frozenset):
        for m in x:
            out.extend(_features_of(m, kind))
    return out


def _final_pair(stages: Sequence[Stage]) -> Optional[Transferred]:
    w = stages[-1].w
    if len(w) != 1:
        return None
    (x,) = tuple(w)
    return x if isinstance(x, Transferred) else None


def converges_at_ci(stages: Sequence[Stage]) -> bool:
    """D42. A derivation with W_n = {<PHON,SEM>} converges at CI iff SEM is
    interpretable at CI (here: every SEM feature in it is interpretable)."""
    final = _final_pair(stages)
    return final is not None and all(f.interpretable for f in _features_of(final.lf, SEM))


def converges_at_sm(stages: Sequence[Stage]) -> bool:
    """D43. ... converges at SM iff PHON is interpretable at SM."""
    final = _final_pair(stages)
    return final is not None and all(f.interpretable for f in final.pf)


def converges(stages: Sequence[Stage]) -> bool:
    """D44. A derivation converges iff it converges at CI and at SM."""
    return converges_at_ci(stages) and converges_at_sm(stages)


# =====================================================================
# 2. Universal Grammar and I-language (stated last: they name operations)
# =====================================================================

@dataclass(frozen=True)
class UniversalGrammar:
    """D1. UG is a 6-tuple <PHON-F, SYN-F, SEM-F, Select, Merge, Transfer>."""
    phon: FrozenSet[Feature]
    syn: FrozenSet[Feature]
    sem: FrozenSet[Feature]
    select: Any = select
    merge: Any = triggered_merge
    transfer: Any = transfer


def universal_grammar(lex: Lexicon) -> UniversalGrammar:
    return UniversalGrammar(
        phon=frozenset(f for li in lex for f in li.phon),
        syn=frozenset(f for li in lex for f in li.syn),
        sem=frozenset(f for li in lex for f in li.sem),
    )


@dataclass(frozen=True)
class ILanguage:
    """D4. An I-language is a pair <Lex, UG>."""
    lex: Lexicon
    ug: UniversalGrammar


# =====================================================================
# Derivation driver
# =====================================================================

@dataclass
class Step:
    op: str
    detail: str
    stage: Stage


TRANSFER_NTC_KEY = "T8 No Tampering at Transfer steps"


class Derivation:
    """A derivation (D14/D38) that validates itself against the axioms.

    Every method appends a stage and asserts that the previous stage derives
    it by one of the clauses of D38(iii), so a Derivation object cannot be
    built except by operations the paper licenses.
    """

    def __init__(self, lex: Lexicon, la: Iterable[LIToken], merge_rule: Any = None):
        self.lex = lex
        self.merge_rule = merge_rule or triggered_merge
        s0 = Stage(frozenset(la), frozenset())
        self.steps: List[Step] = [Step("init", "<LA, {}>", s0)]

    # -- bookkeeping --------------------------------------------------
    @property
    def stage(self) -> Stage:
        return self.steps[-1].stage

    @property
    def stages(self) -> List[Stage]:
        return [s.stage for s in self.steps]

    @property
    def root(self) -> SO:
        if len(self.stage.w) != 1:
            raise ValueError(f"workspace has {len(self.stage.w)} roots")
        return next(iter(self.stage.w))

    def _push(self, op: str, detail: str, s2: Stage) -> "Derivation":
        s1 = self.stage
        assert derives(s1, s2, self.merge_rule), \
            f"{op} does not satisfy D14/D38:\n  {s1}\n  {s2}"
        self.steps.append(Step(op, detail, s2))
        return self

    # -- operations ---------------------------------------------------
    def select(self, name: str, k: int) -> "Derivation":
        tok = self.lex.token(name, k)
        return self._push("Select", repr(tok), select(tok, self.stage))

    def merge(self, A: SO, B: SO) -> "Derivation":
        kind = "internal Merge" if is_internal_merge(A, B) else "external Merge"
        s2 = apply_merge(self.stage, A, B, merge_rule=self.merge_rule)
        return self._push("Merge", f"{kind}: {_brief(A)} + {_brief(B)}", s2)

    def merge_roots(self) -> "Derivation":
        """External Merge of the two roots of a two-root workspace, with the
        trigger-bearing one as A."""
        if len(self.stage.w) != 2:
            raise ValueError("merge_roots needs exactly two roots")
        a, b = tuple(self.stage.w)
        if self.merge_rule is merge:
            A, B = (a, b) if isinstance(a, frozenset) else (b, a)
        else:
            A, B = (a, b) if triggers(a) else (b, a)
        return self.merge(A, B)

    def select_and_merge(self, name: str, k: int) -> "Derivation":
        """Select a token and immediately merge it with the (single) root."""
        self.select(name, k)
        return self.merge_roots()

    def internal_merge(self, target: SO) -> "Derivation":
        """Internal Merge of `target` with the root that contains it."""
        root = self.root
        if not contains(root, target):
            raise ValueError(f"{target!r} is not contained in the root (T14: PIC)")
        return self.merge(root, target)

    def cyclic_transfer(self) -> "Derivation":
        so = self.root
        if untransferred_inner_phases(so):
            raise ValueError("Transfer undefined: contains a strong phase whose "
                             "complement has not been transferred (D38)")
        new = cyclic_transfer(so)
        s2 = Stage(self.stage.la, (self.stage.w - {so}) | {new})
        return self._push("Cyclic-Transfer", _brief(new), s2)

    def transfer(self) -> "Derivation":
        so = self.root
        if not is_strong_phase(so):
            raise ValueError(f"Transfer undefined: {so!r} is not a strong phase (D38)")
        if untransferred_inner_phases(so):
            raise ValueError("Transfer undefined: contains a strong phase whose "
                             "complement has not been transferred (D38)")
        new = transfer(so, so)
        s2 = Stage(self.stage.la, (self.stage.w - {so}) | {new})
        return self._push("Transfer", repr(new), s2)

    # -- checks -------------------------------------------------------
    def check(self) -> dict:
        st = self.stages
        merges = [i for i, s in enumerate(self.steps) if s.op == "Merge"]
        syntactic = [i for i, s in enumerate(self.steps)
                     if s.op in ("Merge", "Select") and i > 0]
        transfers = [i for i, s in enumerate(self.steps)
                     if s.op in ("Transfer", "Cyclic-Transfer")]
        # T7 is a theorem about the Select/Merge part of a derivation (section
        # 6); Cyclic-Transfer can remove a lower occurrence.  Check it on the
        # stages before the first Transfer step.
        first_t = transfers[0] if transfers else len(self.steps)
        pre = self.steps[:first_t]
        ops = [s.detail.split(":")[0] if s.op == "Merge" else s.op for s in pre]
        last_syn = [s.stage for s in pre]
        res = {
            "D14/D38 derivation": is_derivation(st, self.lex, self.merge_rule),
            "D15 LA_n = {} and W_n = {A}": derived_object(st, self.lex, self.merge_rule) is not None,
            "T5 binary branching": all(is_binary_branching(x) for x in st[-1].w),
            "T6 unique root occurrences": all(unique_root_occurrences(s.w) for s in st),
            "T7 two occurrences iff internal Merge": two_occurrences_iff_internal_merge(
                last_syn, ops),
            "T8 No Tampering (Select/Merge)": all(
                satisfies_ntc(st[i - 1], st[i]) for i in syntactic),
            "T9 Extension (at every Merge)": all(
                satisfies_extension(st[i - 1], st[i]) for i in merges),
            "T10 Inclusiveness": satisfies_inclusiveness(st),
        }
        # Section 8: Cyclic-Transfer in the plug-back-in model violates the NTC.
        res[TRANSFER_NTC_KEY] = all(satisfies_ntc(st[i - 1], st[i]) for i in transfers)
        return res

    # -- display ------------------------------------------------------
    def pretty(self) -> str:
        lines = []
        for i, s in enumerate(self.steps):
            lines.append(f"{i:>3}. {s.op:<16} {s.detail}")
            # sorted: the workspace is a frozenset, so an unsorted join makes
            # the printed trace depend on PYTHONHASHSEED.
            lines.append(
                f"     W = {{{', '.join(sorted(_brief(x) for x in s.stage.w))}}}")
        return "\n".join(lines)


class NTCDerivation(Derivation):
    """A derivation run with the section 12 (NTC-respecting) Transfer.

    Merge and Select are unchanged.  Transfer never touches the workspace; it
    only extends the functions PF and LF, so the No-Tampering Condition holds
    at every step and the structure that reaches the interfaces is exactly the
    one Merge built.  `reading` picks how "W minus those already transferred"
    is understood (see the section 12 banner).
    """

    def __init__(self, lex: Lexicon, la: Iterable[LIToken], merge_rule: Any = None,
                 reading: str = "occurrence"):
        super().__init__(lex, la, merge_rule)
        self.ntc = NTCStage(self.stage.la, self.stage.w)
        self.reading = reading
        self.interfaces: Optional[Transferred] = None

    def _sync(self) -> None:
        self.ntc = NTCStage(self.stage.la, self.stage.w, self.ntc.pf, self.ntc.lf)

    def merge(self, A: SO, B: SO) -> "NTCDerivation":
        if contains(A, B):
            if not any(is_accessible(p, self.ntc.domain(), self.reading)
                       for p in positions(B, A)):
                raise ValueError(
                    f"Merge cannot apply to {B!r}: it is not in the accessible part "
                    "of the workspace (T14, section 12 version)")
        super().merge(A, B)
        self._sync()
        return self

    def select(self, name: str, k: int) -> "NTCDerivation":
        super().select(name, k)
        self._sync()
        return self

    def cyclic_transfer(self) -> "NTCDerivation":
        self.ntc = cyclic_transfer_ntc(self.ntc, self.root)
        pf = self.ntc.pf[-1][1]
        detail = "PF, LF += " + (" ".join(f.name for f in pf) or "(zero)")
        self.steps.append(Step("Cyclic-Transfer", detail, self.stage))
        return self

    def transfer(self) -> "NTCDerivation":
        self.interfaces = transfer_ntc(self.ntc, self.root)
        self.steps.append(Step("Transfer", repr(self.interfaces), self.stage))
        return self

    def check(self) -> dict:
        res = super().check()
        syntactic = [s.stage for s in self.steps if s.op in ("init", "Select", "Merge")]
        res["D14 derivation (Select/Merge stages only)"] = is_derivation(
            syntactic, self.lex, self.merge_rule)
        return res


# =====================================================================
# Display helpers (no theoretical content)
# =====================================================================

def _brief(X: Any) -> str:
    if isinstance(X, (LIToken, Transferred, LFObject)):
        return repr(X)
    if isinstance(X, frozenset):
        try:
            head, other = projector(X)
            return "{" + _brief(head) + ", " + _brief(other) + "}"
        except ValueError:
            return "{" + ", ".join(sorted(_brief(m) for m in X)) + "}"
    return repr(X)


def labelled_bracket(root: SO, path: Optional[Path] = None) -> str:
    """Labelled bracketing of one occurrence, with non-final occurrences
    (D40) shown in angle brackets."""
    if path is None:
        path = (root,)
    X = path[-1]
    if isinstance(X, (Transferred, LFObject)):
        return repr(X)
    nonfinal = is_nonfinal_occurrence(path, root)
    if isinstance(X, LIToken):
        return f"<{X!r}>" if nonfinal else repr(X)
    lab = label(X)
    cat = lab.li.cat or lab.li.name
    tag = cat + "P" if is_maximal_projection(X, root) else cat + "'"
    inner = " ".join(labelled_bracket(root, path + (k,)) for k in ordered_children(X))
    return f"<[{tag} {inner}]>" if nonfinal else f"[{tag} {inner}]"


def fmt_lf(x: Any) -> str:
    """Readable rendering of a TransferLF output (D39)."""
    if isinstance(x, LFObject):
        names = sorted(f.name for f in x.sem)
        return (",".join(names) if names else "0") + f"_{x.k}"
    if isinstance(x, frozenset):
        return "{" + ", ".join(sorted(fmt_lf(m) for m in x)) + "}"
    return repr(x)


def pf_string(pf: Sequence[Feature]) -> str:
    return " ".join(f.name for f in pf) or "(silence)"


def linear_order(X: SO) -> str:
    """Spell out a complete phase via TransferPF (D41)."""
    return pf_string(transfer_pf(X, X))


def ordered_children(X: FrozenSet[SO]) -> List[SO]:
    """Children of X in Specifier-Head-Complement order (D41b)."""
    head, other = projector(X)
    return [head, other] if isinstance(head, LIToken) else [other, head]

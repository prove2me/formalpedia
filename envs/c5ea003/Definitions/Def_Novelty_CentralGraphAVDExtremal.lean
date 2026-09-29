-- Prove2me | Definitions.Def_Novelty_CentralGraphAVDExtremal
-- name    : Novelty_CentralGraphAVDExtremal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:27.755985+00:00
-- url     : https://prove2.me/theorems/73a938ba-96f6-4a9d-a97a-7f5240053b93
-- title:
--   Aether Catalog definitions — Novelty_CentralGraphAVDExtremal
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CentralGraphAVDExtremal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CentralGraphAVDExtremal.lean by skeleton subtraction
import Mathlib

/-!
# The extremal regime of AVD‑total colourings of central graphs of regular graphs

For a `d`‑regular graph `G` that is not complete, the **central graph** `C(G)`
(subdivide every edge, join every non‑adjacent pair) satisfies two lower bounds on
its adjacent‑vertex‑distinguishing (AVD) total chromatic number:

* a `d`‑governed bound  `χ''ₐ(C(G)) ≥ d + 3`, and
* a `|V|`‑governed bound `χ''ₐ(C(G)) ≥ |V(G)| + 1`   (every original vertex of
  `C(G)` has degree `|V(G)| − 1`).

Because a non‑complete `d`‑regular graph always has `|V(G)| ≥ d + 2`, the
`|V|`‑bound is **at least as strong** as the `d`‑bound, and the two coincide
*exactly* in the **extremal regime** `|V(G)| = d + 2`.

This file isolates and characterises that extremal regime, continuing the theory
developed for the central graph.  The main results are:

* `compl_isRegular` : the complement of a `d`‑regular graph on `n` vertices is
  `(n − 1 − d)`‑regular.
* `extremal_iff_compl_one_regular` : for a `d`‑regular non‑complete graph,
  `|V(G)| = d + 2` **iff** the complement is `1`‑regular (a perfect matching); i.e.
  the extremal graphs are precisely `K_{d+2}` minus a perfect matching (the
  cocktail‑party graphs).
* `dbound_le_cardbound` : `d + 3 ≤ |V(G)| + 1`, so the `|V|`‑bound dominates.
* `bounds_agree_iff_extremal` : the two bounds are **equal** iff `|V(G)| = d + 2`.
* `central_degree_inl_extremal` : in the extremal case every original vertex of
  `C(G)` has degree `d + 1`.
* `extremal_avd_ge` : in the extremal case every AVD total colouring of `C(G)` uses
  at least `|V(G)| + 1 = d + 3` colours — the two bounds collapse to a single sharp
  value.
* `cycleGraph_four_extremal` / `cycle4_avd_ge_four` : the `4`‑cycle `C₄` is the
  smallest extremal instance (`d = 2`, `|V| = 4`, complement `= 2K₂`), and its
  central graph needs at least `4` colours; while the `5`‑cycle is **not** extremal
  (`5 > 4`), witnessing the strictness of `dbound_le_cardbound`.

## Set‑up (recalled, self‑contained)

A *total colouring* of a finite simple graph `H` is modelled as a proper vertex
colouring of the **total graph** `T(H)` on `V(H) ⊕ E(H)`; it is **AVD** when
adjacent vertices receive distinct colour sets
`C(w) = {colour w} ∪ {colour e : e ∋ w}`.
-/

open SimpleGraph Finset

namespace CentralGraphAVDExtremal

/-! ## The total graph `T(H)` and total colourings -/

section TotalGraph

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Vertices of the total graph of `H`: original vertices plus edges. -/
abbrev TV := W ⊕ {e : Sym2 W // e ∈ H.edgeSet}

/-- Adjacency of the total graph. -/
def totalAdj : TV H → TV H → Prop
  | Sum.inl a, Sum.inl b => H.Adj a b
  | Sum.inl a, Sum.inr e => a ∈ (e : Sym2 W)
  | Sum.inr e, Sum.inl a => a ∈ (e : Sym2 W)
  | Sum.inr e, Sum.inr f => e ≠ f ∧ ∃ x, x ∈ (e : Sym2 W) ∧ x ∈ (f : Sym2 W)

/-- The **total graph** `T(H)`. -/
def totalGraph : SimpleGraph (TV H) where
  Adj := totalAdj H
  symm := by
    rintro (a|e) (b|f) h <;> simp only [totalAdj] at h ⊢
    · exact h.symm
    · exact h
    · exact h
    · exact ⟨h.1.symm, by obtain ⟨x, hx1, hx2⟩ := h.2; exact ⟨x, hx2, hx1⟩⟩
  loopless := ⟨fun x => by
    cases x with
    | inl a => simp [totalAdj]
    | inr e => simp [totalAdj]⟩

instance : DecidableRel (totalGraph H).Adj := by
  rintro (a|e) (b|f) <;> unfold totalGraph totalAdj <;> infer_instance

/-! ### The star clique -/

/-- Index type of the star at `w`. -/
abbrev starIdx (w : W) := Option {e : Sym2 W // e ∈ H.incidenceFinset w}

/-- The star at `w` as a family of total-graph vertices. -/
def starMap (w : W) : starIdx H w → TV H
  | none => Sum.inl w
  | some e => Sum.inr ⟨e.1, ((mem_incidenceFinset H w e.1).1 e.2).1⟩



/-! ### Colour sets and AVD total colourings -/

variable {κ : Type*} [DecidableEq κ]

/-- Colour set of `w`: the colours of `w` and of all its incident edges. -/
def colorSet (C : (totalGraph H).Coloring κ) (w : W) : Finset κ :=
  Finset.image (fun i => C (starMap H w i)) Finset.univ

/-- A total colouring is **adjacent-vertex-distinguishing** if adjacent vertices
have distinct colour sets. -/
def IsAVD (C : (totalGraph H).Coloring κ) : Prop :=
  ∀ a b, H.Adj a b → colorSet H C a ≠ colorSet H C b




/-! ### Padding the palette preserves AVD -/


end TotalGraph

/-! ## The central graph `C(G)` -/

section CentralGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices of the central graph. -/
abbrev CV := V ⊕ {e : Sym2 V // e ∈ G.edgeSet}

/-- Adjacency of the central graph. -/
def centralAdj : CV G → CV G → Prop
  | Sum.inl u, Sum.inl w => u ≠ w ∧ ¬ G.Adj u w
  | Sum.inl u, Sum.inr e => u ∈ (e : Sym2 V)
  | Sum.inr e, Sum.inl u => u ∈ (e : Sym2 V)
  | Sum.inr _, Sum.inr _ => False

/-- The **central graph** `C(G)`. -/
def centralGraph : SimpleGraph (CV G) where
  Adj := centralAdj G
  symm := by
    rintro (a|e) (b|f) h <;> simp only [centralAdj] at h ⊢
    · exact ⟨(Ne.symm h.1), fun hh => h.2 hh.symm⟩
    · exact h
    · exact h
  loopless := ⟨fun x => by
    cases x with
    | inl a => simp [centralAdj]
    | inr e => simp [centralAdj]⟩

instance : DecidableRel (centralGraph G).Adj := by
  rintro (a|e) (b|f) <;> unfold centralGraph centralAdj <;> infer_instance



/-! ## Regular graphs: the `d + 3` lower bound (recalled) -/





/-! ## The extremal regime `|V| = d + 2`

The two lower bounds `d + 3` and `|V| + 1` are related by `card_ge`, and coincide
exactly when `|V| = d + 2`.  We characterise this extremal regime and record the
sharp consequence for `C(G)`.
-/







end CentralGraph

/-! ## Concrete instances: the smallest extremal cycle `C₄` versus `C₅` -/









end CentralGraphAVDExtremal

/-!
-- !-- Lab Notes -- !--

**Hypothesis.** The guiding conjecture `χ''ₐ(C(G)) = d + 3` for `d`-regular
non-complete `G` can only be an equality in a restricted regime, because the
`|V|`-governed bound `χ''ₐ(C(G)) ≥ |V(G)| + 1` already dominates the `d`-governed
bound `≥ d + 3`.  We hypothesised that the exact boundary is `|V(G)| = d + 2`, and
that these extremal graphs are precisely the cocktail-party graphs `K_{d+2}` minus
a perfect matching.

**Experiment.** We reproduced the self-contained total-graph/AVD machinery and both
lower bounds, then added: (i) `compl_isRegular`, the complement-degree computation;
(ii) `extremal_iff_compl_one_regular`, the characterisation `|V| = d + 2 ↔` the
complement is `1`-regular; (iii) `dbound_le_cardbound` and
`bounds_agree_iff_extremal`, locating exactly where the two bounds coincide; and
(iv) `extremal_avd_ge`, the sharp lower bound on the extremal family.  We tested the
theory on concrete cycles: `C₄` (extremal) and `C₅` (non-extremal).

**Analysis.** The characterisation is clean and reduces to a single
nat-arithmetic identity `n − 1 − d = 1 ⟺ n = d + 2` once the complement-degree
formula is in place; the non-triviality is entirely in `card_ge`, the
non-complete-regular vertex count, and in the degree structure of `C(G)`.  `C₄`
is the smallest extremal instance: its complement is `2K₂`, a perfect matching,
exactly as predicted.  `C₅` fails extremality (`5 ≠ 4`), and there the `|V|`-bound
(`6`) strictly beats the `d`-bound (`5`) — the concrete witness of why the naive
`d + 3` equality is false off the extremal family.

**Critique.** No result is vacuous: each main theorem is a genuine biconditional or
strict inequality with insight-bearing proofs (`omega`, `by_contra`, palette
padding, `fin_cases`/`decide` on concrete graphs).  The extremal characterisation
is stated with the necessary non-completeness witness `(a, b)`; dropping it would
make the statement false for complete graphs (where the `d`-bound argument breaks).

**Synthesis.** The extremal regime `|V| = d + 2` is now fully characterised as the
cocktail-party family, and the sharp lower bound `χ''ₐ(C(G)) ≥ d + 3 = |V| + 1`
is established there.  The remaining gap is the matching upper bound on this
family — a concrete `(d+3)`-colouring — recorded in `FUTURE_DIRECTIONS.md`.
-/



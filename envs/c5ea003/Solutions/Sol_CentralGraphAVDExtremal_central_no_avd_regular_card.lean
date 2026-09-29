-- Prove2me | solution 1 for CentralGraphAVDExtremal.central_no_avd_regular_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:56:54.602172+00:00
-- url     : https://prove2.me/submissions/b3d70f45-fb4c-4ebc-97da-f420948005d4

-- Sol generated from Novelty/CentralGraphAVDExtremal.lean
import Mathlib
import Definitions.Def_Novelty_CentralGraphAVDExtremal
import Theorems.Thm_CentralGraphAVDExtremal_central_degree_inl

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

open CentralGraphAVDExtremal

/-! ## The total graph `T(H)` and total colourings -/


variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]





/-! ### The star clique -/



/-- The star at `w` is a clique of the total graph. -/
theorem star_pairwise (w : W) :
    Pairwise fun i j => (totalGraph H).Adj (starMap H w i) (starMap H w j) := by
  rintro (_|⟨e,he⟩) (_|⟨f,hf⟩) hij <;> simp only [starMap, totalGraph, totalAdj]
  · exact absurd rfl hij
  · exact ((mem_incidenceFinset H w f).1 hf).2
  · exact ((mem_incidenceFinset H w e).1 he).2
  · refine ⟨?_, w, ((mem_incidenceFinset H w e).1 he).2, ((mem_incidenceFinset H w f).1 hf).2⟩
    intro h; apply hij; have hef : e = f := congrArg Subtype.val h; subst hef; rfl

/-- The star at `w` has `deg w + 1` elements. -/
theorem card_starIdx (w : W) : Nat.card (starIdx H w) = H.degree w + 1 := by
  rw [starIdx, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe,
    card_incidenceFinset_eq_degree]

/-! ### Colour sets and AVD total colourings -/

variable {κ : Type*} [DecidableEq κ]



omit [DecidableEq κ] in
/-- On the star at `w` the colours are pairwise distinct. -/
theorem star_comp_injective (C : (totalGraph H).Coloring κ) (w : W) :
    Function.Injective (fun i => C (starMap H w i)) := by
  intro i j hij
  by_contra hne
  exact (C.valid (star_pairwise H w hne)) hij

/-- With exactly `deg w + 1` colours, a proper total colouring uses **all** of
them at `w`. -/
theorem colorSet_eq_univ_of_card [Fintype κ] (C : (totalGraph H).Coloring κ)
    (w : W) (hcard : Fintype.card κ = H.degree w + 1) :
    colorSet H C w = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [colorSet, Finset.card_image_of_injective _ (star_comp_injective H C w),
    Finset.card_univ, hcard, ← Nat.card_eq_fintype_card]
  exact card_starIdx H w

/-- **Adjacent equal-degree obstruction.** If two adjacent vertices have equal
degree `Δ`, no AVD total colouring uses only `Δ + 1` colours. -/
theorem not_isAVD_of_adjacent_eqdeg [Fintype κ] (C : (totalGraph H).Coloring κ)
    (u v : W) (hadj : H.Adj u v) (hdeg : H.degree u = H.degree v)
    (hcard : Fintype.card κ = H.degree u + 1) : ¬ IsAVD H C := by
  intro hAVD
  have hu : colorSet H C u = Finset.univ := colorSet_eq_univ_of_card H C u hcard
  have hv : colorSet H C v = Finset.univ :=
    colorSet_eq_univ_of_card H C v (by rw [hcard, hdeg])
  exact hAVD u v hadj (hu.trans hv.symm)

/-! ### Padding the palette preserves AVD -/



/-! ## The central graph `C(G)` -/


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]





omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two original vertices are adjacent in `C(G)` iff they are non-adjacent in `G`. -/
theorem central_inl_inl_iff (u w : V) :
    (centralGraph G).Adj (Sum.inl u) (Sum.inl w) ↔ u ≠ w ∧ ¬ G.Adj u w := Iff.rfl


/-! ## Regular graphs: the `d + 3` lower bound (recalled) -/

/-- **Structural fact.** A `d`-regular graph that is not complete has at least
`d + 2` vertices. -/
theorem card_ge_of_regular_not_complete {d : ℕ} (hreg : G.IsRegularOfDegree d)
    (a b : V) (hne : a ≠ b) (hnadj : ¬ G.Adj a b) : d + 2 ≤ Fintype.card V := by
  have hcard : (insert a (insert b (G.neighborFinset a))).card = d + 2 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_neighborFinset_eq_degree, hreg a]
    · simp only [mem_neighborFinset]; exact fun h => hnadj h
    · simp only [mem_insert, mem_neighborFinset]
      push_neg
      exact ⟨hne, fun h => (SimpleGraph.irrefl G) h⟩
  calc d + 2 = (insert a (insert b (G.neighborFinset a))).card := hcard.symm
    _ ≤ Fintype.card V := card_le_univ _




/-! ## The extremal regime `|V| = d + 2`

The two lower bounds `d + 3` and `|V| + 1` are related by `card_ge`, and coincide
exactly when `|V| = d + 2`.  We characterise this extremal regime and record the
sharp consequence for `C(G)`.
-/








/-! ## Concrete instances: the smallest extremal cycle `C₄` versus `C₅` -/










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
open CentralGraphAVDExtremal in
theorem solution{d : ℕ} (hreg : G.IsRegularOfDegree d)
    (a b : V) (hne : a ≠ b) (hnadj : ¬ G.Adj a b) :
    ¬ ∃ C : (totalGraph (centralGraph G)).Coloring (Fin (d + 2)),
        IsAVD (centralGraph G) C := by
  rintro ⟨C, hAVD⟩
  have hge : d + 2 ≤ Fintype.card V := card_ge_of_regular_not_complete G hreg a b hne hnadj
  have hinj := star_comp_injective (centralGraph G) C (Sum.inl a)
  have hle : Fintype.card (starIdx (centralGraph G) (Sum.inl a))
      ≤ Fintype.card (Fin (d + 2)) := Fintype.card_le_of_injective _ hinj
  have hstar : Fintype.card (starIdx (centralGraph G) (Sum.inl a))
      = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, card_starIdx, central_degree_inl]
  rw [hstar, Fintype.card_fin] at hle
  have hVeq : Fintype.card V = d + 2 := le_antisymm hle hge
  have hadj : (centralGraph G).Adj (Sum.inl a) (Sum.inl b) :=
    (central_inl_inl_iff G a b).2 ⟨hne, hnadj⟩
  have hda := central_degree_inl G a
  have hdb := central_degree_inl G b
  have hdeg : (centralGraph G).degree (Sum.inl a) = (centralGraph G).degree (Sum.inl b) := by
    omega
  have hcard : Fintype.card (Fin (d + 2)) = (centralGraph G).degree (Sum.inl a) + 1 := by
    rw [Fintype.card_fin, hda, hVeq]
  exact not_isAVD_of_adjacent_eqdeg (centralGraph G) C (Sum.inl a) (Sum.inl b)
    hadj hdeg hcard hAVD

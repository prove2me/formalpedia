-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.not_fanRaspaud_of_oddCut_singleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:00:10.057693+00:00
-- url     : https://prove2.me/submissions/34653b77-f00b-4622-a56d-d5828c9431b1

-- Sol generated from Bridges/InfiniteCubicMatchings.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_card_inter_cutEdges_odd
/-
# Perfect matching conjectures in (possibly infinite) cubic bridgeless graphs

This file develops a formal framework, valid for **arbitrary** (finite or infinite) vertex
types, for the three classical perfect-matching conjectures on cubic bridgeless graphs:

* the **Berge–Fulkerson conjecture** (`BergeFulkerson`): six perfect matchings covering
  every edge exactly twice;
* the **Fan–Raspaud conjecture** (`FanRaspaud`): three perfect matchings with empty
  intersection;
* the **Máčajová–Škoviera conjecture** (`MacajovaSkoviera`): two perfect matchings whose
  intersection contains no odd edge cut.

The main results proved here are

* `PerfectMatching.exists_mem_cutEdges` and `PerfectMatching.card_inter_cutEdges_odd`:
  the *parity lemma* in the infinite setting — a perfect matching meets every edge cut with
  a **finite odd side** in an odd (in particular nonzero) number of edges;
* `BergeFulkerson.fanRaspaud` : BF ⟹ FR;
* `FanRaspaud.macajovaSkoviera` : FR ⟹ MŠ (this is where the parity lemma is used);
* `BergeFulkerson.macajovaSkoviera` : BF ⟹ MŠ;
* `not_bergeFulkerson_of_oddCut_singleton` and friends: all three conjectures **fail** for a
  graph possessing a one-edge cut with a finite odd side (the infinite analogue of "a cubic
  graph with a bridge has no such family"); hence bridgelessness is a necessary hypothesis;
* `ProperThreeEdgeColoring.bergeFulkerson` : a 3-edge-colourable graph satisfies BF (by
  doubling the colour classes) — this works verbatim for infinite graphs;
* transport of all three properties along graph isomorphisms.

Everything is stated for an arbitrary vertex type `V`; no finiteness of `V` is assumed
anywhere.
-/

open Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-! ## Perfect matchings as fixed-point-free involutions -/


open PerfectMatching









/-! ## Edge cuts with a finite side -/






/-! ## A combinatorial lemma: fixed-point-free involutions have even orbit sets -/


/-! ## The parity lemma -/

open PerfectMatching

variable (M : PerfectMatching G)



/-- A perfect matching meets every odd cut. -/
theorem Bridges.InfiniteCubicMatchings.PerfectMatching.exists_mem_cutEdges
    (S : Finset V) (hS : Odd S.card) :
    (M.edges ∩ cutEdges G S).Nonempty := by
  have h := M.card_inter_cutEdges_odd S hS
  rw [Set.nonempty_iff_ne_empty]
  rintro he
  rw [he] at h
  simp at h

/-- A perfect matching meets every odd cut. -/
theorem Bridges.InfiniteCubicMatchings.PerfectMatching.exists_mem_of_isOddCut
    {C : Set (Sym2 V)} (hC : IsOddCut G C) :
    (M.edges ∩ C).Nonempty := by
  obtain ⟨S, hS, rfl⟩ := hC
  exact M.exists_mem_cutEdges S hS


/-! ## The three conjectures -/







/-! ## The implications BF ⟹ FR ⟹ MŠ -/




/-! ## Bridgelessness is necessary: one-edge odd cuts destroy all three properties -/

/-- Every perfect matching contains an edge forming a one-edge odd cut (the infinite
analogue of "every perfect matching contains every bridge"). -/
theorem Bridges.InfiniteCubicMatchings.mem_edges_of_isOddCut_singleton
    (M : PerfectMatching G) {e : Sym2 V}
    (h : IsOddCut G {e}) : e ∈ M.edges := by
  obtain ⟨f, hf, hfe⟩ := M.exists_mem_of_isOddCut h
  rwa [Set.mem_singleton_iff.mp hfe] at hf





/-! ## 3-edge-colourable graphs satisfy Berge–Fulkerson -/


/-! ## Invariance under isomorphism -/

open PerfectMatching

variable {W : Type v} {H : SimpleGraph W}











open Bridges.InfiniteCubicMatchings in
theorem solution{e : Sym2 V} (h : IsOddCut G {e}) :
    ¬ FanRaspaud G := by
  rintro ⟨M, hM⟩
  have : e ∈ (M 0).edges ∩ (M 1).edges ∩ (M 2).edges :=
    ⟨⟨mem_edges_of_isOddCut_singleton _ h, mem_edges_of_isOddCut_singleton _ h⟩,
      mem_edges_of_isOddCut_singleton _ h⟩
  rw [hM] at this
  exact this

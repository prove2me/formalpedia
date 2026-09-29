-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.ProperThreeEdgeColoring.bergeFulkerson
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:26:09.382931+00:00
-- url     : https://prove2.me/submissions/2f13e4b9-87ba-4c49-b8f4-64c9c522bf6a

-- Sol generated from Bridges/InfiniteCubicMatchings.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
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






/-! ## The three conjectures -/







/-! ## The implications BF ⟹ FR ⟹ MŠ -/




/-! ## Bridgelessness is necessary: one-edge odd cuts destroy all three properties -/






/-! ## 3-edge-colourable graphs satisfy Berge–Fulkerson -/


/-! ## Invariance under isomorphism -/

open PerfectMatching

variable {W : Type v} {H : SimpleGraph W}











open Bridges.InfiniteCubicMatchings in
theorem solution(h : ProperThreeEdgeColoring G) :
    BergeFulkerson G := by
  obtain ⟨M, hdisj, hcover⟩ := h
  refine ⟨fun i => M ⟨i.1 / 2, by omega⟩, ?_⟩
  intro e hE
  obtain ⟨i₀, hi₀⟩ := hcover e hE
  have key : {i : Fin 6 | e ∈ (M ⟨i.1 / 2, by omega⟩).edges} = {i : Fin 6 | i.1 / 2 = i₀.1} := by
    ext i
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hi
      by_contra hne
      have : (⟨i.1 / 2, by omega⟩ : Fin 3) ≠ i₀ := by
        intro hEq
        exact hne (congrArg Fin.val hEq)
      exact (hdisj _ _ this).le_bot ⟨hi, hi₀⟩
    · intro hi
      have : (⟨i.1 / 2, by omega⟩ : Fin 3) = i₀ := Fin.ext hi
      rw [this]
      exact hi₀
  rw [key]
  have hc : ∀ j : Fin 3, {i : Fin 6 | i.1 / 2 = j.1}.ncard = 2 := by
    intro j
    simp only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    revert j
    decide
  exact hc i₀

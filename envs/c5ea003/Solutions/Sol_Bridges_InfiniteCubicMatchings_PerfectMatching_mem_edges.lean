-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.PerfectMatching.mem_edges
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:18:35.31423+00:00
-- url     : https://prove2.me/submissions/0c4df37f-5c84-44a0-8247-224f568bb919

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











open Bridges.InfiniteCubicMatchings.PerfectMatching in
@[simp] theorem solution(M : PerfectMatching G) (u w : V) :
    s(u, w) ∈ M.edges ↔ M.partner u = w := by
  constructor
  · rintro ⟨x, hx⟩
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact M.invol _
  · rintro rfl
    exact ⟨u, rfl⟩

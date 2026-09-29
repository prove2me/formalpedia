-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.PerfectMatching.card_inter_cutEdges_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:43:40.717132+00:00
-- url     : https://prove2.me/submissions/60fb3651-710a-4286-b1df-4277f81d4a2e

-- Sol generated from Bridges/InfiniteCubicMatchings.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_inter_cutEdges_eq
import Theorems.Thm_Bridges_InfiniteCubicMatchings_even_card_of_involutive
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




lemma partner_ne (M : PerfectMatching G) (v : V) : M.partner v ≠ v :=
  fun h => G.irrefl (h ▸ M.isAdj v)





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
theorem solution(S : Finset V) (hS : Odd S.card) :
    Odd (M.edges ∩ cutEdges G S).ncard := by
  classical
  have hinj : Set.InjOn (fun v => s(v, M.partner v))
      ↑(S.filter (fun v => M.partner v ∉ S)) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rfl
    · exact absurd hb.1 (by simpa [M.invol] using ha.2)
  rw [inter_cutEdges_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn (by
    simpa using hinj)]
  -- the complementary part of `S` is even, being stable under the partner involution
  have hEven : Even (S.filter (fun v => M.partner v ∈ S)).card := by
    refine even_card_of_involutive _ M.partner ?_ (fun a _ => M.invol a)
      (fun a _ => partner_ne M a)
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.2, by rw [M.invol]; exact ha.1⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun v => M.partner v ∈ S)
  rcases hS with ⟨k, hk⟩
  rcases hEven with ⟨m, hm⟩
  refine ⟨k - m, ?_⟩
  omega

-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.even_card_of_involutive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:20:15.178279+00:00
-- url     : https://prove2.me/submissions/689a61a2-00b3-474c-aa09-b4fb5e308a86

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
theorem solution{α : Type*} [DecidableEq α] (s : Finset α) (f : α → α)
    (hmaps : ∀ a ∈ s, f a ∈ s) (hinv : ∀ a ∈ s, f (f a) = a) (hne : ∀ a ∈ s, f a ≠ a) :
    Even s.card := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  subst hn
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
  · simp
  · have hfa : f a ∈ s := hmaps a ha
    have hane : f a ≠ a := hne a ha
    set t : Finset α := s \ {a, f a} with ht
    have hsub : ({a, f a} : Finset α) ⊆ s := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair : ({a, f a} : Finset α).card = 2 := Finset.card_pair (Ne.symm hane)
    have hcardt : t.card = s.card - 2 := by
      rw [ht, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hpair]
    have h2 : 2 ≤ s.card := by
      have := Finset.card_le_card hsub
      rw [hpair] at this
      exact this
    have hmaps' : ∀ b ∈ t, f b ∈ t := by
      intro b hb
      rw [ht, Finset.mem_sdiff] at hb ⊢
      obtain ⟨hbs, hbn⟩ := hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbn ⊢
      refine ⟨hmaps b hbs, ?_, ?_⟩
      · intro h
        exact hbn.2 (by rw [← h, hinv b hbs])
      · intro h
        exact hbn.1 (by
          have := congrArg f h
          rwa [hinv b hbs, hinv a ha] at this)
    have hinv' : ∀ b ∈ t, f (f b) = b := fun b hb => hinv b (Finset.mem_sdiff.mp hb).1
    have hne' : ∀ b ∈ t, f b ≠ b := fun b hb => hne b (Finset.mem_sdiff.mp hb).1
    obtain ⟨m, hm⟩ := ih t.card (by omega) t hmaps' hinv' hne' rfl
    exact ⟨m + 1, by omega⟩

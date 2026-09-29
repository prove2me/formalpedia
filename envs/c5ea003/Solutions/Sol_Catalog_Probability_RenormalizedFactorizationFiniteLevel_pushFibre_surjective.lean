-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationFiniteLevel.pushFibre_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:51:56.432386+00:00
-- url     : https://prove2.me/submissions/e0554adb-637a-4ea2-843a-c895be753a6a

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationFiniteLevel
open Catalog.Probability.RenormalizedFactorizationFiniteLevel in
theorem solution {U : Type*} [CommGroup U] {V : Type*} [CommGroup V] (φ : U →* V)
    (hφ : Function.Surjective φ) (n : ℕ) (g : U) :
    Function.Surjective (pushFibre φ n g) := by
  rintro ⟨h, hh⟩
  choose a ha using hφ
  -- lift slots `1..n` pointwise and let slot `0` absorb the discrepancy
  refine ⟨⟨Fin.cons (g * (∏ j : Fin n, a (h j.succ))⁻¹) (fun j => a (h j.succ)), ?_⟩, ?_⟩
  · rw [Fin.prod_univ_succ]
    simp
  · apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [pushFibre, Fin.cons_zero, map_mul, map_inv, map_prod, ha]
      rw [Fin.prod_univ_succ] at hh
      rw [← hh, mul_inv_cancel_right]
    · simp [pushFibre, ha]

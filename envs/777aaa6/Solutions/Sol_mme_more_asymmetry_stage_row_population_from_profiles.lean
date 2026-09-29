-- Prove2me | solution 1 for mme_more_asymmetry_stage_row_population_from_profiles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T16:52:07.570115+00:00
-- url     : https://prove2.me/submissions/d0d9c713-e2a6-4311-a913-60d00c86de83

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

open BigOperators MME.MoreAsymmetryExactSeed
set_option autoImplicit false

theorem solution (t : Fin 45 → Term) (w : Fin 45 → ℕ)
    (ht : ∀ i, (t i).Valid)
    (hw : ∑ i : Fin 45, w i = denominator) :
    (∑ i : Fin 45,
      if (t i).boundary = [] then
        denominator ^ 2 * w i * (t i).region.sum
      else
        denominator ^ 3 * w i) = denominator ^ 4 := by
  classical
  have hrow : ∀ i, (if (t i).boundary = [] then
      denominator ^ 2 * w i * (t i).region.sum
    else denominator ^ 3 * w i) = denominator ^ 3 * w i := by
    intro i
    by_cases hb : (t i).boundary = []
    · have hv := ht i
      simp only [Term.Valid, hb, if_pos] at hv
      have hnorm : (t i).region.sum = denominator := by
        simpa [Normalized] using hv.2.2.2.1
      simp only [hb, if_pos, hnorm]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · simp [hb]
  calc
    _ = ∑ i : Fin 45, denominator ^ 3 * w i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i
    _ = denominator ^ 3 * (∑ i : Fin 45, w i) := by
      rw [← Finset.mul_sum]
    _ = denominator ^ 4 := by
      rw [hw]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

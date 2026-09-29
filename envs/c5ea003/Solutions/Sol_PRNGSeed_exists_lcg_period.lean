-- Prove2me | solution 1 for PRNGSeed.exists_lcg_period
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:49:22.001522+00:00
-- url     : https://prove2.me/submissions/9798d6c1-cfd6-428d-a9c6-b68178b77fa5

import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLCG
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
open PRNGSeed in
theorem solution {R : Type*} [CommRing R] {a b : R} [Fintype R] {ai : R} (hai : ai * a = 1) :
    ∃ p : ℕ, 0 < p ∧ ∀ x : R, (lcgStep a b)^[p] x = x := by
  -- an invertible affine map is injective, hence a permutation of the finite ring
  have hinj : Function.Injective (lcgStep a b) := by
    intro x y h
    simp only [lcgStep] at h
    have h' : a * x = a * y := by linear_combination h
    calc x = ai * (a * x) := by rw [← mul_assoc, hai, one_mul]
      _ = ai * (a * y) := by rw [h']
      _ = y := by rw [← mul_assoc, hai, one_mul]
  let σ : Equiv.Perm R := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  -- a permutation of a finite set has finite order
  refine ⟨orderOf σ, orderOf_pos σ, fun x => ?_⟩
  have h1 : (σ ^ orderOf σ) x = x := by rw [pow_orderOf_eq_one]; rfl
  rw [Equiv.Perm.coe_pow] at h1
  exact h1

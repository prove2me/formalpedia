-- Prove2me | solution 1 for mme_exp_log_two_entropyBits_eq_prod_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:53:54.337342+00:00
-- url     : https://prove2.me/submissions/1f2ac1d6-63d3-451b-a8d8-eebc2fa05575

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_modern_entropy_data

open BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- The exponential of Shannon entropy in bits is the usual weighted
geometric reciprocal.  Positivity removes all zero-mass conventions and is
exactly the interior case used by the Stothers profile. -/
theorem mme_exp_log_two_entropyBits_eq_prod_rpow
    {D : Type*} [Fintype D]
    (p : D → ℝ) (hp : ∀ i, 0 < p i) :
    Real.exp (Real.log 2 * mme_modern_entropyBits p) =
      ∏ i, Real.rpow (p i) (-p i) := by
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [show Real.log 2 * mme_modern_entropyBits p =
      ∑ i, -(p i * Real.log (p i)) by
    unfold mme_modern_entropyBits
    rw [mul_div_cancel₀ _ hlog2]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Real.negMulLog_def]
    ring]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [show Real.rpow (p i) (-p i) =
      Real.exp (Real.log (p i) * (-p i)) from
    Real.rpow_def_of_pos (hp i) (-p i)]
  congr 1
  ring

theorem solution
    {D : Type*} [Fintype D]
    (p : D → ℝ) (hp : ∀ i, 0 < p i) :
    Real.exp (Real.log 2 * mme_modern_entropyBits p) =
      ∏ i, Real.rpow (p i) (-p i) := by
  exact mme_exp_log_two_entropyBits_eq_prod_rpow p hp

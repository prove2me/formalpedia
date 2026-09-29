-- Prove2me | solution 1 for mme_integer_step_certified_log_copies_eq_entropy_log
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T00:33:46.370165+00:00
-- url     : https://prove2.me/submissions/40764816-ba38-4656-b734-5a79412c0aee

import Definitions.Def_mme_regional_certified_log_copy_bound
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization
set_option autoImplicit false

/-- The certified recipe budget is the logarithm of the entropy retention
bound minus the repair cost and the log-two integer-rounding allowance. -/
theorem solution
    {ell M : ℕ} {P : ProfiledCW.Predicate M} (D : IntegerStep ell M P) :
    D.certifiedLogCopies = Real.log D.entropyLower - Real.log 2 -
      (D.repairExponent : ℝ) * Real.log 8 := by
  have hp : 0 < polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) := by
    unfold polynomialFactor
    positivity
  have hf : 0 < scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell := by
    unfold scaleFactor loadFactor ambientFactor polynomialFactor
    positivity
  unfold IntegerStep.certifiedLogCopies IntegerStep.entropyLower
  dsimp only
  rw [Real.log_div (Real.exp_ne_zero _) (mul_ne_zero
    (mul_ne_zero (by norm_num) hp.ne') hf.ne'), Real.log_exp]
  rw [show (64 : ℝ) = 2 * 32 by norm_num]
  rw [show 2 * 32 * polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) *
      scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell =
      2 * (32 * polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) *
      scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell) by ring]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_ne_zero
    (mul_ne_zero (by norm_num) hp.ne') hf.ne')]
  ring


#print axioms solution

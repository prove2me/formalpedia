-- Prove2me | Theorems.Thm_mme_prescribed_Z_six_value_of_graded_MM_word_dimensions
-- name    : mme_prescribed_Z_six_value_of_graded_MM_word_dimensions
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T18:47:08.788663+00:00
-- url     : https://prove2.me/theorems/0989f4bb-919b-49ae-8ca9-a895a079351f
-- title:
--   Prescribed-Z entropy value from exact graded matrix dimensions
-- statement:
--   If every exact prescribed-Z power restricts to a one-dimensional-sided matrix tensor whose remaining dimension is the multinomial count times the grade alphabet multiplicities, then its six-symmetric prescribed-Z restriction value is at least exp(tau*(H(p)+sum p_a log d_a)). The result holds for any finite number of grades, any positive multiplicities, any positive tau, and either X-zero or Y-zero matrix orientation.
-- source:
--   Type-class lower bound with polynomial loss, applied to DWZ prescribed-Z six-symmetric restriction certificates, Definitions 3.7 and 8.1.

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Nat.Choose.Multinomial
open MME MME.DWZRestrictedValue Module
open scoped BigOperators
universe u
set_option autoImplicit false

theorem mme_prescribed_Z_six_value_of_graded_MM_word_dimensions
    {K : Type u} [Field K] (T : TensorObj K 3)
    {t : ℕ} {I : Type u} (bZ : Basis I K (T.V 2)) (grade : I → Fin t)
    (p : IntegerZSplitProfile t) (d : Fin t → ℕ) (hd : ∀ a, 0 < d a)
    (tau : ℝ) (htau : 0 < tau)
    (hsource : ∀ m,
      let D := Nat.multinomial Finset.univ (fun a ↦ p.count a * m) *
        ∏ a, d a ^ (p.count a * m)
      TensorObj.Restrict (MMObj K 1 1 D) (prescribedZPower T bZ grade p m) ∨
      TensorObj.Restrict (MMObj K D 1 1) (prescribedZPower T bZ grade p m)) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau
      (Real.exp (tau * ((∑ a, Real.negMulLog ((p.count a : ℝ) / p.denominator)) +
        ∑ a, ((p.count a : ℝ) / p.denominator) * Real.log (d a))))  := by sorry

-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_pi_partial_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:56.447056+00:00
-- url     : https://prove2.me/submissions/95d143f2-dce4-4860-81c7-5af9ce1d1b9e

import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_arctan_partial_error
import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false

/-!
Rational centres for complex phases, with explicit analytic error bounds.
The centres use Machin's formula and a finite exponential Taylor polynomial.
All finite arithmetic is rational.  The bounds depend on two natural-number
precision parameters, and therefore can be checked without a real comparison.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators











/-- Machin's identity turns two rational series into a certified centre of π. -/
theorem p2m_local_recoh_pi_partial_error (n : ℕ) :
    |(recohPiPartial n : ℝ) - Real.pi| ≤ (recohPiError n : ℝ) := by
  have h5 := recoh_arctan_partial_error (1 / 5) (by norm_num) (by norm_num) n
  have h239 := recoh_arctan_partial_error (1 / 239) (by norm_num) (by norm_num) n
  have hpi : Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    rw [inv_eq_one_div, inv_eq_one_div] at h
    linarith
  rw [hpi]
  have he : (recohPiPartial n : ℝ) -
      (16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239)) =
      16 * ((recohArctanPartial (1 / 5) n : ℝ) - Real.arctan (1 / 5)) -
      4 * ((recohArctanPartial (1 / 239) n : ℝ) - Real.arctan (1 / 239)) := by
    simp only [recohPiPartial, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    ring
  rw [he]
  calc
    _ ≤ |16 * ((recohArctanPartial (1 / 5) n : ℝ) - Real.arctan (1 / 5))| +
        |4 * ((recohArctanPartial (1 / 239) n : ℝ) - Real.arctan (1 / 239))| :=
      abs_sub _ _
    _ ≤ (recohPiError n : ℝ) := by
      simp only [abs_mul, show |(16 : ℝ)| = 16 by norm_num,
        show |(4 : ℝ)| = 4 by norm_num]
      simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h5 h239
      simp only [recohPiError, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
      linarith































end Couret.STROBO2TORS


theorem solution : ∀ (n : Nat),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohPiPartial n)) Real.pi))
    (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohPiError n)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_pi_partial_error


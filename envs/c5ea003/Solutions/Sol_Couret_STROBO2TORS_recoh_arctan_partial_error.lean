-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_arctan_partial_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:53.616197+00:00
-- url     : https://prove2.me/submissions/cdbad42e-0247-42fd-992b-097aaf68abb1

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





/-- A geometric tail bound for the rational arctangent polynomial. -/
theorem p2m_local_recoh_arctan_partial_error (x : ℚ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ) :
    |(recohArctanPartial x n : ℝ) - Real.arctan (x : ℝ)| ≤
      (recohArctanError x n : ℝ) := by
  have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast hx₀
  have hx1 : (x : ℝ) < 1 := by exact_mod_cast hx₁
  have hxnorm : ‖(x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hsq : (x : ℝ) ^ 2 < 1 := by nlinarith
  have hterm (k : ℕ) :
      ‖(-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)‖ ≤
        (x : ℝ) * ((x : ℝ) ^ 2) ^ k := by
    rw [norm_div, norm_mul, norm_pow, norm_pow]
    simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hx0]
    have hden : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
    rw [abs_of_nonneg (Nat.cast_nonneg (2 * k + 1))]
    calc
      (x : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ≤ (x : ℝ) ^ (2 * k + 1) :=
        div_le_self (by positivity) hden
      _ = (x : ℝ) * ((x : ℝ) ^ 2) ^ k := by rw [pow_succ, pow_mul]; ring
  have h := norm_sub_le_of_geometric_bound_of_hasSum hsq hterm
    (Real.hasSum_arctan hxnorm) n
  simpa only [recohArctanPartial, recohArctanError, Real.norm_eq_abs,
    Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_add, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h





































end Couret.STROBO2TORS


theorem solution : ∀ (x : Rat),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) x →
    @LT.lt.{0} Rat Rat.instLT x (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) →
      ∀ (n : Nat),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohArctanPartial x n))
              (Real.arctan (@Rat.cast.{0} Real Real.instRatCast x))))
          (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohArctanError x n)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_arctan_partial_error


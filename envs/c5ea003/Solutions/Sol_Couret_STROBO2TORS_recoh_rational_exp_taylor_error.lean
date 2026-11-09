-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_exp_taylor_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:17.922891+00:00
-- url     : https://prove2.me/submissions/715d6723-cb4d-4f0e-b48c-876cae754e23

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_exp_taylor_value
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

































theorem p2m_local_recoh_rational_exp_taylor_error (t : ℚ) (ht : |t| ≤ 8)
    (n : ℕ) (hn : 15 ≤ n) :
    ‖Complex.exp (Complex.I * (t : ℂ)) -
      recohRationalComplexValue (recohRationalExpTaylor t n)‖ ≤ (recohTaylorError n : ℝ) := by
  rw [recoh_rational_exp_taylor_value]
  have ht' : ‖Complex.I * (t : ℂ)‖ ≤ 8 := by
    simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_ratCast] using
      (show |(t : ℝ)| ≤ 8 by exact_mod_cast ht)
  have hn' : (16 : ℝ) ≤ n + 1 := by exact_mod_cast (show 16 ≤ n + 1 by omega)
  have hfrac : ‖Complex.I * (t : ℂ)‖ / n.succ ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n.succ)]
    simp only [Nat.cast_succ]
    linarith
  have h := Complex.exp_bound' hfrac
  calc
    _ ≤ ‖Complex.I * (t : ℂ)‖ ^ n / n.factorial * 2 := h
    _ ≤ (recohTaylorError n : ℝ) := by
      simp only [recohTaylorError, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_ofNat, Rat.cast_natCast]
      calc
        _ ≤ (8 : ℝ) ^ n / n.factorial * 2 := by gcongr
        _ = _ := by ring









end Couret.STROBO2TORS


theorem solution : ∀ (t : Rat),
  @LE.le.{0} Rat Rat.instLE (@abs.{0} Rat Rat.instLattice Rat.addGroup t)
      (@OfNat.ofNat.{0} Rat (nat_lit 8) (@Rat.instOfNat (nat_lit 8))) →
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))) n →
        @LE.le.{0} Real Real.instLE
          (@Norm.norm.{0} Complex Complex.instNorm
            (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
              (Complex.exp
                (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
                  (@Rat.cast.{0} Complex Complex.instRatCast t)))
              (Couret.STROBO2TORS.recohRationalComplexValue (Couret.STROBO2TORS.recohRationalExpTaylor t n))))
          (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohTaylorError n)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_exp_taylor_error


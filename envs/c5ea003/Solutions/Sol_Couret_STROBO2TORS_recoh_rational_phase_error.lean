-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_phase_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:58:12.225181+00:00
-- url     : https://prove2.me/submissions/eb586b36-2be9-4255-b6b4-3205b7fd693c

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_pi_partial_error
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_exp_taylor_error
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



































theorem recoh_complex_phase_lipschitz (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤ |x - y| := by
  have he : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)





/-- Soundness for every admitted pair of precision parameters and every turn
in the unit interval.  The guard on the rational centre of π is executable. -/
theorem p2m_local_recoh_rational_phase_error (turn : ℚ) (hturn : |turn| ≤ 1)
    (machinTerms taylorTerms : ℕ) (hpi : |recohPiPartial machinTerms| ≤ 4)
    (htaylor : 15 ≤ taylorTerms) :
    ‖Complex.exp (Complex.I * ((2 * Real.pi * (turn : ℝ) : ℝ) : ℂ)) -
      recohRationalComplexValue (recohRationalPhase turn machinTerms taylorTerms)‖ ≤
        (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by
  have hturn' : |(turn : ℝ)| ≤ 1 := by exact_mod_cast hturn
  have hangle : |2 * recohPiPartial machinTerms * turn| ≤ 8 := by
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith [abs_nonneg (recohPiPartial machinTerms), abs_nonneg turn]
  have ht := recoh_rational_exp_taylor_error
    (2 * recohPiPartial machinTerms * turn) hangle taylorTerms htaylor
  have hp := recoh_pi_partial_error machinTerms
  have hl := recoh_complex_phase_lipschitz (2 * Real.pi * (turn : ℝ))
    (2 * (recohPiPartial machinTerms : ℝ) * (turn : ℝ))
  have hab : |2 * Real.pi * (turn : ℝ) -
      2 * (recohPiPartial machinTerms : ℝ) * (turn : ℝ)| ≤
      2 * (recohPiError machinTerms : ℝ) := by
    rw [show 2 * Real.pi * (turn : ℝ) - 2 * (recohPiPartial machinTerms : ℝ) * (turn : ℝ) =
      2 * (Real.pi - (recohPiPartial machinTerms : ℝ)) * (turn : ℝ) by ring,
      abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num, abs_sub_comm]
    calc
      _ ≤ 2 * |(recohPiPartial machinTerms : ℝ) - Real.pi| * 1 := by gcongr
      _ ≤ _ := by linarith
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (Complex.exp (Complex.I * ((2 * Real.pi * (turn : ℝ) : ℝ) : ℂ)))
    (Complex.exp (Complex.I * ((2 * (recohPiPartial machinTerms : ℝ) * (turn : ℝ) : ℝ) : ℂ)))
    (recohRationalComplexValue (recohRationalPhase turn machinTerms taylorTerms))
  simp only [recohRationalPhase] at htri ⊢
  simp only [recohRationalPhaseError, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  push_cast at ht htri hl ⊢
  linarith

end Couret.STROBO2TORS


theorem solution : ∀ (turn : Rat),
  @LE.le.{0} Rat Rat.instLE (@abs.{0} Rat Rat.instLattice Rat.addGroup turn)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) →
    ∀ (machinTerms taylorTerms : Nat),
      @LE.le.{0} Rat Rat.instLE
          (@abs.{0} Rat Rat.instLattice Rat.addGroup (Couret.STROBO2TORS.recohPiPartial machinTerms))
          (@OfNat.ofNat.{0} Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4))) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))) taylorTerms →
          @LE.le.{0} Real Real.instLE
            (@Norm.norm.{0} Complex Complex.instNorm
              (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                (Complex.exp
                  (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
                    ↑(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          Real.pi)
                        (@Rat.cast.{0} Real Real.instRatCast turn))))
                (Couret.STROBO2TORS.recohRationalComplexValue
                  (Couret.STROBO2TORS.recohRationalPhase turn machinTerms taylorTerms))))
            (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohRationalPhaseError machinTerms taylorTerms)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_phase_error


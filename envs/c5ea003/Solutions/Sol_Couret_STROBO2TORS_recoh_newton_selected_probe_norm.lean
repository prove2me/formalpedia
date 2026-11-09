-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_newton_selected_probe_norm
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:17.339481+00:00
-- url     : https://prove2.me/submissions/af520f28-60ca-4cbd-85a6-9cd5e3a63a1e

import Definitions.Def_Couret_RecohTripleNewton_821bcf694d07
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_cubes_norm_lower
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Quantitative Newton identity for three unit complex numbers, and the
two-choice rational protocol used to replace a character by itself or its
cube before any support reading is measured.

The cube reading is the sum of the cubes of the three values. It is not the
cube of their sum. No distinctness of the values is assumed.

The rational comparison below is executable. Its correctness theorem takes
an explicit approximation certificate; this module does not construct that
certificate or establish extensionality for arbitrary approximation routines.
-/

namespace Couret.STROBO2TORS











/-- The square-norm threshold used in the rejecting branch avoids square roots.
This strict bound is weaker than the sharp analytic estimate but suffices for
the certified two-choice protocol. -/
theorem recoh_triple_cubes_norm_gt_one (z₁ z₂ z₃ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1)
    (hsmall : ‖z₁ + z₂ + z₃‖ ^ 2 < 1 / 2) :
    1 < ‖z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3‖ := by
  have hzero := norm_nonneg (z₁ + z₂ + z₃)
  have hone : ‖z₁ + z₂ + z₃‖ ≤ 1 := by nlinarith
  have hcube : ‖z₁ + z₂ + z₃‖ ^ 3 ≤ ‖z₁ + z₂ + z₃‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hone (sq_nonneg ‖z₁ + z₂ + z₃‖)]
  have hbound := recoh_triple_cubes_norm_lower z₁ z₂ z₃ h₁ h₂ h₃
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - ‖z₁ + z₂ + z₃‖ ^ 2)] at hbound
  linarith













theorem recoh_newton_selected_probe_of_accept (z₁ z₂ z₃ : ℂ) (m : ℚ)
    (hm : (3 / 8 : ℚ) ≤ m) :
    recohNewtonSelectedProbe z₁ z₂ z₃ m = z₁ + z₂ + z₃ := by
  simp [recohNewtonSelectedProbe, recohNewtonMultiplier, hm]

theorem recoh_newton_selected_probe_of_reject (z₁ z₂ z₃ : ℂ) (m : ℚ)
    (hm : m < (3 / 8 : ℚ)) :
    recohNewtonSelectedProbe z₁ z₂ z₃ m = z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3 := by
  simp [recohNewtonSelectedProbe, recohNewtonMultiplier, not_le.mpr hm]

/-- A rational approximation to the square norm suffices for a certified
choice. The certificate permits equality at its error bound. -/
theorem p2m_local_recoh_newton_selected_probe_norm (z₁ z₂ z₃ : ℂ) (m : ℚ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1)
    (hcert : |(m : ℝ) - ‖z₁ + z₂ + z₃‖ ^ 2| ≤ 1 / 8) :
    (1 / 2 : ℝ) ≤ ‖recohNewtonSelectedProbe z₁ z₂ z₃ m‖ := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcert
  by_cases hm : (3 / 8 : ℚ) ≤ m
  · rw [recoh_newton_selected_probe_of_accept z₁ z₂ z₃ m hm]
    have hmreal : (3 / 8 : ℝ) ≤ (m : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hm
    have hsquare : (1 / 4 : ℝ) ≤ ‖z₁ + z₂ + z₃‖ ^ 2 := by linarith
    have hzero := norm_nonneg (z₁ + z₂ + z₃)
    by_contra hlt
    have hlt' : ‖z₁ + z₂ + z₃‖ < (1 / 2 : ℝ) := lt_of_not_ge hlt
    have hp := mul_pos (sub_pos.mpr hlt')
      (show 0 < (1 / 2 : ℝ) + ‖z₁ + z₂ + z₃‖ by positivity)
    nlinarith
  · have hm' : m < (3 / 8 : ℚ) := lt_of_not_ge hm
    rw [recoh_newton_selected_probe_of_reject z₁ z₂ z₃ m hm']
    have hmreal : (m : ℝ) < (3 / 8 : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hm'
    have hsquare : ‖z₁ + z₂ + z₃‖ ^ 2 < (1 / 2 : ℝ) := by linarith
    have hcube := recoh_triple_cubes_norm_gt_one z₁ z₂ z₃ h₁ h₂ h₃ hsquare
    linarith



end Couret.STROBO2TORS


theorem solution : ∀ (z₁ z₂ z₃ : Complex) (m : Rat),
  @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₁)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₂)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₃)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @LE.le.{0} Real Real.instLE
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@Rat.cast.{0} Real Real.instRatCast m)
                (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                  (@Norm.norm.{0} Complex Complex.instNorm
                    (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) z₁ z₂) z₃))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 8)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))) →
          @LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@Norm.norm.{0} Complex Complex.instNorm (Couret.STROBO2TORS.recohNewtonSelectedProbe z₁ z₂ z₃ m)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_newton_selected_probe_norm


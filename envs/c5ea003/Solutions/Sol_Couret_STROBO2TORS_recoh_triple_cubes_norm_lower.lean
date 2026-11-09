-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_triple_cubes_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:19.376966+00:00
-- url     : https://prove2.me/submissions/07e53485-d66e-4388-b117-4917bc412188

import Definitions.Def_Couret_RecohTripleNewton_821bcf694d07
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_newton_identity
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





/-- Reverse triangle inequality for the Newton decomposition. -/
theorem p2m_local_recoh_triple_cubes_norm_lower (z₁ z₂ z₃ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) :
    3 * |1 - ‖z₁ + z₂ + z₃‖ ^ 2| - ‖z₁ + z₂ + z₃‖ ^ 3 ≤
      ‖z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3‖ := by
  have hn := recoh_triple_newton_identity z₁ z₂ z₃ h₁ h₂ h₃
  have hb : 3 * (z₁ * z₂ * z₃) * ((1 - ‖z₁ + z₂ + z₃‖ ^ 2 : ℝ) : ℂ) =
      (z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3) - (z₁ + z₂ + z₃) ^ 3 := by
    rw [hn]
    ring
  have ht := norm_sub_le (z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3) ((z₁ + z₂ + z₃) ^ 3)
  rw [← hb] at ht
  simp only [norm_mul, norm_pow, h₁, h₂, h₃, Complex.norm_real,
    Real.norm_eq_abs] at ht
  norm_num at ht
  linarith



























end Couret.STROBO2TORS


theorem solution : ∀ (z₁ z₂ z₃ : Complex),
  @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₁)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₂)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₃)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @LE.le.{0} Real Real.instLE
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                    (@Norm.norm.{0} Complex Complex.instNorm
                      (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) z₁ z₂)
                        z₃))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
              (@Norm.norm.{0} Complex Complex.instNorm
                (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) z₁ z₂) z₃))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@Norm.norm.{0} Complex Complex.instNorm
            (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
              (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                  (@instHPow.{0, 0} Complex Nat
                    (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                  z₁ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                  (@instHPow.{0, 0} Complex Nat
                    (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                  z₂ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                (@instHPow.{0, 0} Complex Nat
                  (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                z₃ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_triple_cubes_norm_lower


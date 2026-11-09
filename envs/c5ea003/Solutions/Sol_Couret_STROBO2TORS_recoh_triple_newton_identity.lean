-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_triple_newton_identity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:11.173131+00:00
-- url     : https://prove2.me/submissions/88879b20-37a7-456a-92fc-7db0e046adcf

import Definitions.Def_Couret_RecohTripleNewton_821bcf694d07
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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

private theorem recoh_unit_mul_conj (z : ℂ) (hz : ‖z‖ = 1) :
    z * star z = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- The Newton identity, specialized to three unit complex values. -/
theorem p2m_local_recoh_triple_newton_identity (z₁ z₂ z₃ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) :
    z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3 =
      (z₁ + z₂ + z₃) ^ 3 +
        3 * (z₁ * z₂ * z₃) * ((1 - ‖z₁ + z₂ + z₃‖ ^ 2 : ℝ) : ℂ) := by
  have hu₁ := recoh_unit_mul_conj z₁ h₁
  have hu₂ := recoh_unit_mul_conj z₂ h₂
  have hu₃ := recoh_unit_mul_conj z₃ h₃
  have he₂ : z₁ * z₂ + z₁ * z₃ + z₂ * z₃ =
      (z₁ * z₂ * z₃) * star (z₁ + z₂ + z₃) := by
    simp only [star_add]
    linear_combination -(z₂ * z₃) * hu₁ - (z₁ * z₃) * hu₂ - (z₁ * z₂) * hu₃
  have hnorm : (z₁ + z₂ + z₃) * star (z₁ + z₂ + z₃) =
      ((‖z₁ + z₂ + z₃‖ ^ 2 : ℝ) : ℂ) := by
    rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc
    z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3 =
        (z₁ + z₂ + z₃) ^ 3 -
          3 * (z₁ + z₂ + z₃) * (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) +
          3 * (z₁ * z₂ * z₃) := by ring
    _ = (z₁ + z₂ + z₃) ^ 3 +
        3 * (z₁ * z₂ * z₃) * ((1 - ‖z₁ + z₂ + z₃‖ ^ 2 : ℝ) : ℂ) := by
      rw [he₂, Complex.ofReal_sub, Complex.ofReal_one, ← hnorm]
      ring





























end Couret.STROBO2TORS


theorem solution : ∀ (z₁ z₂ z₃ : Complex),
  @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₁)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₂)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₃)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @Eq.{1} Complex
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
              z₃ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@HPow.hPow.{0, 0, 0} Complex Nat Complex
              (@instHPow.{0, 0} Complex Nat
                (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
              (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) z₁ z₂) z₃)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
              (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                (@OfNat.ofNat.{0} Complex (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Complex (nat_lit 3) Complex.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) z₁ z₂) z₃))
              ↑(@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                    (@Norm.norm.{0} Complex Complex.instNorm
                      (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) z₁ z₂)
                        z₃))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_triple_newton_identity


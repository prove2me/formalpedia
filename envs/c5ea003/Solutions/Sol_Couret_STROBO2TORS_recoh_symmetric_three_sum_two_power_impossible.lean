-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_symmetric_three_sum_two_power_impossible
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:42:49.530101+00:00
-- url     : https://prove2.me/submissions/37ef877b-385c-4578-a105-7587c9072fe4

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Couret_STROBO2TORS_recoh_three_root_symmetry_excludes_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_power_cube_one_implies_one

set_option autoImplicit false

/-!
An algebraic bridge towards three-term non-cancellation for 2-primary
complex characters. hpair is an EXPLICIT hypothesis and is NOT yet
derived here from unit-modulus roots and conjugation.
-/

namespace Couret.STROBO2TORS

/-- A normalized vanishing three-term sum with the conjugate symmetric
condition forces a nontrivial cube root. -/
theorem recoh_symmetric_three_sum_cube
    (b c : ℂ)
    (hsum : 1 + b + c = 0)
    (hpair : b + c + b * c = 0) :
    b ^ 3 = 1 := by
  have hc : c = -1 - b := by
    linear_combination hsum
  have hquadratic : b ^ 2 + b + 1 = 0 := by
    rw [hc] at hpair
    linear_combination -hpair
  calc
    b ^ 3 = 1 + (b - 1) * (b ^ 2 + b + 1) := by ring
    _ = 1 := by rw [hquadratic]; ring

/-- Algebraic impossibility of a 2-power root of unity in a
nontrivial symmetric vanishing three-root configuration. -/
theorem p2m_local_recoh_symmetric_three_sum_two_power_impossible
    (n : ℕ) (b c : ℂ)
    (hpow : b ^ (2 ^ n) = 1)
    (hsum : 1 + b + c = 0)
    (hpair : b + c + b * c = 0) : False := by
  have hcube : b ^ 3 = 1 :=
    recoh_symmetric_three_sum_cube b c hsum hpair
  have hb : b = 1 :=
    recoh_two_power_cube_one_implies_one n b hpow hcube
  exact (recoh_three_root_symmetry_excludes_one b c hsum hpair) hb

end Couret.STROBO2TORS


theorem solution : ∀ (n : Nat) (b c : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
        b
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
    @Eq.{1} Complex
        (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) b)
          c)
        (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) →
      @Eq.{1} Complex
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) b c)
            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) b c))
          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) →
        False := @_root_.Couret.STROBO2TORS.p2m_local_recoh_symmetric_three_sum_two_power_impossible


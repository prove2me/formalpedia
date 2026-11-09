-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_squared_choice_energy_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:03:58.100141+00:00
-- url     : https://prove2.me/submissions/33a97644-c189-4a28-ad72-377e34331d19

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_find_some
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_predicate_choice_spec
import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

/-!
# Deterministic certified selection of an odd power

The executable search examines the rational approximations in ascending
index order, accepts the first value at least `3/2`, and falls back to index
zero.  Index `j` represents the odd character power `2*j+1`.

The contract uses an absolute error at most `1/2` on squared magnitude.
The root equations imply the dichotomy required to justify the fallback;
the selector never needs the hidden phases or an opposite-pair witness.
Constructing the rational approximations from a canonical square is a
separate obligation.  Extensionality below states the precise interface
that such a deterministic approximation procedure must satisfy.
-/

namespace Couret.STROBO2TORS













/-- The selected index is valid, including the explicit fallback, when `m>0`. -/
theorem recoh_odd_power_choice_lt (m : ℕ) (hm : 0 < m) (approx : ℕ → ℚ) :
    recohOddPowerChoice m approx < m := by
  cases hfind : recohOddPowerFind approx (List.range m) with
  | none => simpa [recohOddPowerChoice, hfind] using hm
  | some j =>
      have hj := (recoh_odd_power_find_some approx (List.range m) j hfind).1
      simpa [recohOddPowerChoice, hfind] using (List.mem_range.mp hj)













/-- A Boolean-test choice stays in the odd-power index range. -/
theorem recoh_odd_predicate_choice_lt (m : ℕ) (hm : 0 < m) (accept : ℕ → Bool) :
    recohOddPredicateChoice m accept < m :=
  recoh_odd_power_choice_lt m hm _





/-- Generic certified acceptance protocol.  This also supports comparing
the rational squared norm of a complex centre against `9/4`, without
computing a square root. -/
theorem recoh_odd_predicate_choice_energy_ge_one
    (m : ℕ) (hm : 0 < m) (energy : ℕ → ℝ) (accept : ℕ → Bool)
    (haccept : ∀ j < m, accept j = true → 1 ≤ energy j)
    (hlarge : ∀ j < m, 3 ≤ energy j → accept j = true)
    (hdich : (∀ j < m, energy j = 1) ∨ ∃ j < m, 3 ≤ energy j) :
    1 ≤ energy (recohOddPredicateChoice m accept) := by
  have hindex := recoh_odd_predicate_choice_lt m hm accept
  rcases recoh_odd_predicate_choice_spec m accept with hpass | ⟨hzero, hfail⟩
  · exact haccept _ hindex hpass
  · rcases hdich with hall | ⟨j, hj, he⟩
    · rw [hall _ hindex]
    · have : false = true := (hfail j hj).symm.trans (hlarge j hj he)
      cases this









/-- The squared-centre protocol is certified by a complex error radius
`1/2`.  Here `actual j` is the square transform, so its norm is the reading
energy.  Approximation error applies to the complex centre, not its squared
norm. -/
theorem p2m_local_recoh_odd_squared_choice_energy_ge_one
    (m : ℕ) (hm : 0 < m) (energy : ℕ → ℝ)
    (actual centre : ℕ → ℂ) (sqNorm : ℕ → ℚ)
    (henergy : ∀ j < m, ‖actual j‖ = energy j)
    (hsq : ∀ j < m, (sqNorm j : ℝ) = ‖centre j‖ ^ 2)
    (herror : ∀ j < m, ‖centre j - actual j‖ ≤ (1 / 2 : ℝ))
    (hdich : (∀ j < m, energy j = 1) ∨ ∃ j < m, 3 ≤ energy j) :
    1 ≤ energy (recohOddSquaredChoice m sqNorm) := by
  apply recoh_odd_predicate_choice_energy_ge_one m hm energy
    (fun j => decide ((9 / 4 : ℚ) ≤ sqNorm j))
  · intro j hj hpass
    have hthreshold : (9 / 4 : ℚ) ≤ sqNorm j := of_decide_eq_true hpass
    have hthresholdReal : (9 / 4 : ℝ) ≤ (sqNorm j : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr hthreshold
    rw [hsq j hj] at hthresholdReal
    have hcentre : (3 / 2 : ℝ) ≤ ‖centre j‖ := by
      nlinarith [norm_nonneg (centre j)]
    have htriangle := norm_sub_norm_le (centre j) (actual j)
    rw [henergy j hj] at htriangle
    have herr := herror j hj
    linarith
  · intro j hj hlarge
    apply decide_eq_true
    have htriangle := norm_sub_norm_le (actual j) (centre j)
    rw [henergy j hj, norm_sub_rev] at htriangle
    have herr := herror j hj
    have hcentre : (5 / 2 : ℝ) ≤ ‖centre j‖ := by linarith
    have hthresholdReal : (9 / 4 : ℝ) ≤ (sqNorm j : ℝ) := by
      rw [hsq j hj]
      nlinarith
    exact (Rat.cast_le (K := ℝ)).mp (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hthresholdReal)
  · exact hdich



end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀ (energy : Nat → Real) (actual centre : Nat → Complex) (sqNorm : Nat → Rat),
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j m → @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm (actual j)) (energy j)) →
        (∀ (j : Nat),
            @LT.lt.{0} Nat instLTNat j m →
              @Eq.{1} Real (@Rat.cast.{0} Real Real.instRatCast (sqNorm j))
                (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                  (@Norm.norm.{0} Complex Complex.instNorm (centre j))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
          (∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j m →
                @LE.le.{0} Real Real.instLE
                  (@Norm.norm.{0} Complex Complex.instNorm
                    (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) (centre j)
                      (actual j)))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
            Or
                (∀ (j : Nat),
                  @LT.lt.{0} Nat instLTNat j m →
                    @Eq.{1} Real (energy j) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                (@Exists.{1} Nat fun j =>
                  And (@LT.lt.{0} Nat instLTNat j m)
                    (@LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (energy j))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (energy (Couret.STROBO2TORS.recohOddSquaredChoice m sqNorm)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_squared_choice_energy_ge_one


-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:43:04.597825+00:00
-- url     : https://prove2.me/submissions/d8ce9bad-48e1-4899-8ac4-156ca10ae7dc

import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealTwoPrimeKernel
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Two-generator separation for arbitrary real bases

The long paper allows real generators greater than one. Integer floors and
integer powers retain that literal domain, including nonintegral bases.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
noncomputable section





theorem floor_logb_two_powers_left {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i j : ℕ) :
    ⌊Real.logb p (p ^ i * q ^ j)⌋ = (i : ℤ) + ⌊Real.logb p (q ^ j)⌋ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  rw [Real.logb_mul (pow_ne_zero i hp0) (pow_ne_zero j hq0),
    Real.logb_pow p p i, Real.logb_self_eq_one hp, mul_one,
    Int.floor_natCast_add]

theorem floor_logb_two_powers_right {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i j : ℕ) :
    ⌊Real.logb q (p ^ i * q ^ j)⌋ = ⌊Real.logb q (p ^ i)⌋ + (j : ℤ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  rw [Real.logb_mul (pow_ne_zero i hp0) (pow_ne_zero j hq0),
    Real.logb_pow q q j, Real.logb_self_eq_one hq, mul_one,
    Int.floor_add_natCast]

/-- The literal outer-product identity for every real pair of bases above one. -/
theorem realTwoPrimeKernel_eq_outer_product {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i j : ℕ) :
    realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  unfold realTwoPrimeKernel realTwoPrimeHeight
  rw [floor_logb_two_powers_left hp hq, floor_logb_two_powers_right hp hq,
    zpow_add₀ hp0, zpow_add₀ hq0]
  simp only [zpow_natCast, mul_inv_rev]
  ring

/-- All two-by-two minors vanish, with no integrality assumption on the bases. -/
theorem realTwoPrimeKernel_minor_two_eq_zero {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i i' j j' : ℕ) :
    realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
      realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0 := by
  simp only [realTwoPrimeKernel_eq_outer_product hp hq]
  ring
end
end ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0) :=
  ⟨realTwoPrimeKernel_eq_outer_product hp hq,
    realTwoPrimeKernel_minor_two_eq_zero hp hq⟩

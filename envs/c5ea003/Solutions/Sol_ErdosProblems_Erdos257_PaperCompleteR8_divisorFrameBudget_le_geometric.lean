-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.divisorFrameBudget_le_geometric
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:55:44.15467+00:00
-- url     : https://prove2.me/submissions/2f194a92-03a2-40ce-a37d-87200ce98027

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_reciprocal_divisor_prime_product
import Mathlib
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

/-!
# Divisor-product masses and the separating host's weighted frame budget

The reciprocal divisor sum is computed from the actual prime product. Its
exponential upper bound and the prescribed harmonic scales give a summable
sequence of literal dyadic frame weights. Identifying these literal weights
with the finite-prime weighted term uses the odd-cofactor valuation identity;
the divergent logarithmic moment is a separate remaining step.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset







/-- Harmonic mass bounds the actual reciprocal divisor sum. -/
theorem reciprocal_divisor_prime_product_le_exp (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) ≤
      Real.exp (∑ p ∈ P, (1 : ℝ) / p) := by
  rw [reciprocal_divisor_prime_product P hP, Real.exp_sum]
  apply prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp ((1 : ℝ) / p)
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : (∑ p ∈ P, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    divisorFrameBudget P k ≤ 6 * (3 / 16 : ℝ) ^ k := by
  let n : ℕ := 2 ^ k
  have hn : 0 < n := Nat.pow_pos (by decide)
  have hnum : (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) ≤ 3 * (3 : ℝ) ^ n := by
    have he := (reciprocal_divisor_prime_product_le_exp P hP).trans (Real.exp_le_exp.mpr hS)
    have hpow : Real.exp ((2 : ℝ) ^ k) = Real.exp 1 ^ n := by
      simpa [n] using Real.exp_nat_mul 1 (2 ^ k)
    rw [Real.exp_add, hpow] at he
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
    have hmul := mul_le_mul hp Real.exp_one_lt_three.le (Real.exp_pos 1).le (by positivity : (0 : ℝ) ≤ 3 ^ n)
    exact he.trans (by simpa [mul_comm] using hmul)
  have hpowid : (2 : ℝ) ^ (2 ^ (k + 2) : ℕ) = (16 : ℝ) ^ n := by
    have hi : (2 : ℕ) ^ (k + 2) = 4 * n := by dsimp [n]; rw [pow_add]; ring
    rw [hi, pow_mul]
    norm_num
  have hbig : (2 : ℝ) ≤ (16 : ℝ) ^ n := by
    have hh := le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 16) hn.ne'
    linarith
  have hden : (0 : ℝ) < (16 : ℝ) ^ n - 1 := by linarith
  have hhalf : (16 : ℝ) ^ n / 2 ≤ (16 : ℝ) ^ n - 1 := by linarith
  have hbound : divisorFrameBudget P k ≤ 6 * (3 / 16 : ℝ) ^ n := by
    unfold divisorFrameBudget
    rw [hpowid]
    calc
      _ ≤ (3 * (3 : ℝ) ^ n) / ((16 : ℝ) ^ n - 1) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (3 * (3 : ℝ) ^ n) / ((16 : ℝ) ^ n / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
      _ = _ := by rw [div_pow]; ring
  have hkn : k ≤ n := (show k < 2 ^ k from Nat.lt_two_pow_self).le
  have hlast := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 16)
    (by norm_num : (3 / 16 : ℝ) ≤ 1) hkn
  exact hbound.trans (mul_le_mul_of_nonneg_left hlast (by norm_num))
end

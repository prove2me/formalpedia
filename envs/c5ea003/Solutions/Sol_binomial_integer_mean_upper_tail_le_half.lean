-- Prove2me | solution 1 for binomial_integer_mean_upper_tail_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T22:37:53.407314+00:00
-- url     : https://prove2.me/submissions/2e66eb8b-b13c-460a-b643-9325d5be6c3b

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_matrix_completion_fixed_cardinality
import Theorems.Thm_Fcdf_at_one_ge_half
import Theorems.Thm_binomial_upper_tail_complement_reflect

set_option autoImplicit false
open scoped BigOperators
open Finset MatrixCompletion

theorem solution (N m : ℕ) (h : m < N) :
    ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k ((m : ℝ) / (N : ℝ)) ≤ (1 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0 edge: B2LHS = 0
    subst hm0
    have hz : ∀ k ∈ Finset.Ioo 0 (N+1),
        binomialCardinalityProb N k (((0:ℕ) : ℝ) / (N:ℝ)) = 0 := by
      intro k hk
      rw [Finset.mem_Ioo] at hk
      unfold binomialCardinalityProb
      rw [Nat.cast_zero, zero_div, zero_pow (by omega : k ≠ 0)]
      ring
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]; norm_num
  · -- 1 ≤ m
    have hm1 : 1 ≤ m := hmpos
    -- bridge at p = m/N
    have hbr := binomial_upper_tail_complement_reflect N m (le_of_lt h) ((m:ℝ)/(N:ℝ))
    -- Fcdf(1) ≥ 1/2
    have hge := Fcdf_at_one_ge_half N m h hm1
    -- Fcdf(1) = ∑_{Ico (N-m) (N+1)} bcp N k (1 - m/N)
    -- Fcdf(1) summand uses exp(-(log(N/m)*1)) = m/N
    have hexp : Real.exp (-(Real.log ((N:ℝ)/m) * 1)) = (m:ℝ)/(N:ℝ) := by
      have hNpos : (0:ℝ) < N := by
        have : (0:ℕ) < N := lt_of_lt_of_le hmpos (le_of_lt h)
        exact_mod_cast this
      have hmpos' : (0:ℝ) < m := by exact_mod_cast hm1
      rw [mul_one, ← Real.log_inv, Real.exp_log (by positivity)]
      rw [inv_div]
    -- index: (N-m-1)+1 = N-m
    have hidx : (N-m-1)+1 = N - m := by omega
    -- rewrite the Fcdf sum into the bridge LHS form
    have hFcdf_eq : (∑ k ∈ Finset.Ico ((N-m-1)+1) (N+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ k
            * (Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ (N - k))
        = ∑ k ∈ Finset.Ico (N-m) (N+1), binomialCardinalityProb N k (1 - (m:ℝ)/(N:ℝ)) := by
      rw [hidx]
      apply Finset.sum_congr rfl
      intro k _
      unfold binomialCardinalityProb
      rw [hexp]
      rw [show (1:ℝ) - (1 - (m:ℝ)/(N:ℝ)) = (m:ℝ)/(N:ℝ) by ring]
    rw [hFcdf_eq] at hge
    rw [hbr] at hge
    linarith [hge]

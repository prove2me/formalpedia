-- Prove2me | solution 1 for binomial_lower_tail_weighted_sum_lower_bound_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T08:34:52.933196+00:00
-- url     : https://prove2.me/submissions/33b2c32c-eba5-496e-b7c6-99bb2da36c01

import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

theorem solution
    (N m : ℕ) (p a : ℝ) (f : ℕ → ℝ) :
    0 ≤ p → p ≤ 1 → m ≤ N → 0 ≤ a →
    (∀ k : ℕ, 0 ≤ f k) →
    (∀ k : ℕ, k ≤ m → a ≤ f k) →
    (1 / 2 : ℝ) ≤ binomialLowerTailProb N m p →
    (1 / 2) * a ≤
      ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p * f k := by
  intro hp hp_one hm ha hf_nonneg hf_lower htail
  have hone_minus_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_one
  have hprob_nonneg : ∀ k : ℕ, 0 ≤ binomialCardinalityProb N k p := by
    intro k
    unfold binomialCardinalityProb
    positivity
  have hsubset : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have htail_part_le_full :
      (∑ k ∈ Finset.range (m + 1), binomialCardinalityProb N k p * f k) ≤
        ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p * f k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro k _hkN _hkm
        exact mul_nonneg (hprob_nonneg k) (hf_nonneg k))
  have ha_tail_le_weighted_tail :
      binomialLowerTailProb N m p * a ≤
        ∑ k ∈ Finset.range (m + 1), binomialCardinalityProb N k p * f k := by
    unfold binomialLowerTailProb
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    have hk_le_m : k ≤ m := by
      rw [Finset.mem_range] at hk
      omega
    exact mul_le_mul_of_nonneg_left (hf_lower k hk_le_m) (hprob_nonneg k)
  have hhalf_le_tail :
      (1 / 2 : ℝ) * a ≤ binomialLowerTailProb N m p * a := by
    exact mul_le_mul_of_nonneg_right htail ha
  exact le_trans hhalf_le_tail
    (le_trans ha_tail_le_weighted_tail htail_part_le_full)

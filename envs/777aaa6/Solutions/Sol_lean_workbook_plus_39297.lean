-- Prove2me | solution 1 for lean_workbook_plus_39297
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:50:04.285015+00:00
-- url     : https://prove2.me/submissions/9f452c4a-000e-4b22-a8bc-a45db3cfc2e0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Filter Topology

theorem ancestor_contraction_weighted_bound {E : Type*} [SeminormedAddCommGroup E]
    (x : ℕ → E) (N : ℕ)
    (h : ∀ n, N ≤ n → ∃ k, k < n ∧ n ≤ 2 * k ∧ ‖x n‖ ≤ ‖x k‖ / 2) (n : ℕ) :
    (n : ℝ) * ‖x n‖ ≤ ∑ k ∈ Finset.range N, (k : ℝ) * ‖x k‖ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N
    · exact Finset.single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg k) (norm_nonneg _))
        (Finset.mem_range.mpr hn)
    · obtain ⟨k, hk, hscale, hnorm⟩ := h n (Nat.le_of_not_gt hn)
      have hscale' : (n : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hscale
      have hp := mul_le_mul_of_nonneg_right hscale' (norm_nonneg (x k))
      calc
        (n : ℝ) * ‖x n‖ ≤ (n : ℝ) * (‖x k‖ / 2) :=
          mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n)
        _ ≤ (k : ℝ) * ‖x k‖ := by linarith
        _ ≤ ∑ k ∈ Finset.range N, (k : ℝ) * ‖x k‖ := ih k hk

theorem ancestor_contraction_rate {E : Type*} [SeminormedAddCommGroup E]
    (x : ℕ → E) (N : ℕ)
    (h : ∀ n, N ≤ n → ∃ k, k < n ∧ n ≤ 2 * k ∧ ‖x n‖ ≤ ‖x k‖ / 2)
    (n : ℕ) (hn : 0 < n) :
    ‖x n‖ ≤ (∑ k ∈ Finset.range N, (k : ℝ) * ‖x k‖) / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hn').mpr
  simpa only [mul_comm] using ancestor_contraction_weighted_bound x N h n

theorem ancestor_contraction_tendsto_zero {E : Type*} [SeminormedAddCommGroup E]
    (x : ℕ → E) (N : ℕ)
    (h : ∀ n, N ≤ n → ∃ k, k < n ∧ n ≤ 2 * k ∧ ‖x n‖ ≤ ‖x k‖ / 2) :
    Tendsto x atTop (𝓝 0) := by
  let C := ∑ k ∈ Finset.range N, (k : ℝ) * ‖x k‖
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp ht).const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg (x n))) _ hi
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ancestor_contraction_rate x N h n hn

theorem real_ancestor_halving_hypothesis (x : ℕ → ℝ) (N : ℕ)
    (h : ∀ n, N ≤ n → ∃ k, n / 2 < k ∧ k < n ∧ x n = x k / 2) :
    ∀ n, N ≤ n → ∃ k, k < n ∧ n ≤ 2 * k ∧ ‖x n‖ ≤ ‖x k‖ / 2 := by
  intro n hn
  obtain ⟨k, hk0, hkn, heq⟩ := h n hn
  refine ⟨k, hkn, by omega, ?_⟩
  rw [heq, norm_div, show ‖(2 : ℝ)‖ = 2 by norm_num]

theorem real_ancestor_halving_rate (x : ℕ → ℝ)
    (h : ∀ n, 3 ≤ n → ∃ k, n / 2 < k ∧ k < n ∧ x n = x k / 2)
    (n : ℕ) (hn : 0 < n) : |x n| ≤ (|x 1| + 2 * |x 2|) / (n : ℝ) := by
  have hb := ancestor_contraction_rate x 3 (real_ancestor_halving_hypothesis x 3 h) n hn
  simpa [Finset.sum_range_succ, Real.norm_eq_abs] using hb

theorem real_ancestor_halving_convergence (x : ℕ → ℝ)
    (h : ∀ n, 3 ≤ n → ∃ k, n / 2 < k ∧ k < n ∧ x n = x k / 2) :
    Tendsto x atTop (𝓝 0) :=
  ancestor_contraction_tendsto_zero x 3 (real_ancestor_halving_hypothesis x 3 h)

theorem real_ancestor_halving_epsilon (x : ℕ → ℝ)
    (h : ∀ n, 3 ≤ n → ∃ k, n / 2 < k ∧ k < n ∧ x n = x k / 2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |x n| < ε := by
  intro ε hε
  have ht : Tendsto (fun n => |x n|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using (real_ancestor_halving_convergence x h).norm
  have he : ∀ᶠ n : ℕ in atTop, |x n| < ε := ht.eventually (gt_mem_nhds hε)
  exact eventually_atTop.mp he

theorem index_two_has_no_strict_half_predecessor : ¬ ∃ k : ℕ, 2 / 2 < k ∧ k < 2 := by omega

theorem solution (x : ℕ → ℝ)
    (hx : ∀ n ≥ 2, ∃ k, n / 2 < k ∧ k < n ∧ x n = x k / 2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |x n| < ε := by
  exact real_ancestor_halving_epsilon x (fun n hn => hx n (by omega))

#print axioms ancestor_contraction_weighted_bound
#print axioms ancestor_contraction_rate
#print axioms ancestor_contraction_tendsto_zero
#print axioms real_ancestor_halving_hypothesis
#print axioms real_ancestor_halving_rate
#print axioms real_ancestor_halving_convergence
#print axioms real_ancestor_halving_epsilon
#print axioms index_two_has_no_strict_half_predecessor
#print axioms solution

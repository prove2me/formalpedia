-- Prove2me | solution 1 for fixed_matrix_sampling_log_moment_exponent_window_exists_of_two_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T08:16:51.460424+00:00
-- url     : https://prove2.me/submissions/b9cd052e-977e-49a3-9997-ee2016f7370e

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (β : ℝ) :
    2 < β →
    ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (1 : ℝ) ≤ β * Real.log (↑(max n₁ n₂)) →
      (m : ℝ) ≥ 2 * β * (↑(max n₁ n₂)) *
        Real.log (↑(max n₁ n₂)) →
      ∃ q : ℕ, 1 ≤ q ∧
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) := by
  intro _hβ n₁ n₂ m hn₁ hn₂ _hm hlogWindow hmLower
  let n : ℕ := max n₁ n₂
  let x : ℝ := β * Real.log (n : ℝ)
  let q : ℕ := Nat.ceil x
  have hn_pos_nat : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hx_ge_one : (1 : ℝ) ≤ x := by
    simpa [x, n] using hlogWindow
  have hx_nonneg : 0 ≤ x := le_trans (by norm_num) hx_ge_one
  have hq_lower : x ≤ (q : ℝ) := by
    simpa [q] using Nat.le_ceil x
  have hq_one_real : (1 : ℝ) ≤ (q : ℝ) := le_trans hx_ge_one hq_lower
  have hq_one : 1 ≤ q := by exact_mod_cast hq_one_real
  have hq_lt_add_one : (q : ℝ) < x + 1 := by
    simpa [q] using Nat.ceil_lt_add_one hx_nonneg
  have hq_log_upper : (q : ℝ) ≤ 2 * x := by
    nlinarith
  have hN_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by
    positivity
  have hN_nonneg : 0 ≤ (n₁ : ℝ) * (n₂ : ℝ) := le_of_lt hN_pos
  have hN_le_n_sq :
      (n₁ : ℝ) * (n₂ : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
    have hn₁_le_n_nat : n₁ ≤ n := by
      dsimp [n]
      exact Nat.le_max_left n₁ n₂
    have hn₂_le_n_nat : n₂ ≤ n := by
      dsimp [n]
      exact Nat.le_max_right n₁ n₂
    have hn₁_le_n : (n₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁_le_n_nat
    have hn₂_le_n : (n₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₂_le_n_nat
    nlinarith [mul_le_mul hn₁_le_n hn₂_le_n (by positivity : (0 : ℝ) ≤ n₂) hn_nonneg]
  have hmLower' : (m : ℝ) ≥ 2 * x * (n : ℝ) := by
    simpa [x, n, mul_assoc, mul_left_comm, mul_comm] using hmLower
  have hmn_lower : (m : ℝ) * (n : ℝ) ≥ 2 * x * ((n : ℝ) * (n : ℝ)) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hmLower' hn_nonneg
  have hqN_le :
      (q : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) ≤ (m : ℝ) * (n : ℝ) := by
    have hleft :
        (q : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) ≤
          (2 * x) * ((n₁ : ℝ) * (n₂ : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hq_log_upper hN_nonneg
    have hmiddle :
        (2 * x) * ((n₁ : ℝ) * (n₂ : ℝ)) ≤
          2 * x * ((n : ℝ) * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hN_le_n_sq (by positivity)
    exact le_trans hleft (le_trans hmiddle hmn_lower)
  have hq_sampling :
      (q : ℝ) ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (n : ℝ) := by
    have hrewrite :
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (n : ℝ) =
          ((m : ℝ) * (n : ℝ)) / ((n₁ : ℝ) * (n₂ : ℝ)) := by
      ring
    rw [hrewrite]
    exact (le_div_iff₀ hN_pos).mpr hqN_le
  exact ⟨q, hq_one, by simpa [x, n] using hq_lower,
    by simpa [x, n] using hq_log_upper, by simpa [n] using hq_sampling⟩

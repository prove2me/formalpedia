-- Prove2me | solution 1 for fixed_matrix_sampling_condition_from_sampled_sign_matrix_lambda_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:30.54568+00:00
-- url     : https://prove2.me/submissions/cf390400-adfb-4fbc-b59e-804b8dbddedb

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution
    (β lam : ℝ) (n₁ n₂ r m : ℕ) (μ₁ : ℝ) :
    2 < β → 1 ≤ lam → 0 < r → 1 ≤ μ₁ →
    (m : ℝ) ≥
      lam * μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) *
        (β * Real.log (↑(max n₁ n₂))) →
    (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
      Real.log (↑(max n₁ n₂)) := by
  intro _ hlam hr hμ hm
  by_cases hNzero : max n₁ n₂ = 0
  · simp [hNzero]
  let N : ℝ := (max n₁ n₂ : ℝ)
  let B : ℝ := β * N * Real.log N
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hμsq : 1 ≤ μ₁ ^ 2 := by nlinarith [sq_nonneg (μ₁ - 1)]
  have hlam_nonneg : 0 ≤ lam := le_trans zero_le_one hlam
  have h_lam_mu : 1 ≤ lam * μ₁ ^ 2 := by
    simpa using mul_le_mul hlam hμsq zero_le_one hlam_nonneg
  have h_lam_mu_nonneg : 0 ≤ lam * μ₁ ^ 2 := le_trans zero_le_one h_lam_mu
  have hfactor : 1 ≤ lam * μ₁ ^ 2 * (r : ℝ) := by
    simpa using mul_le_mul h_lam_mu hr1 zero_le_one h_lam_mu_nonneg
  have hlog_nonneg : 0 ≤ Real.log N := by
    have hN_ge_one : (1 : ℝ) ≤ N := by
      have hr_nat : 1 ≤ max n₁ n₂ := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hNzero)
      dsimp [N]
      exact_mod_cast hr_nat
    exact Real.log_nonneg hN_ge_one
  have hB_nonneg : 0 ≤ B := by positivity
  have hscale : B ≤ lam * μ₁ ^ 2 * (r : ℝ) * B :=
    by simpa using mul_le_mul_of_nonneg_right hfactor hB_nonneg
  have hrearrange :
      lam * μ₁ ^ 2 * N * (r : ℝ) * (β * Real.log N) =
        lam * μ₁ ^ 2 * (r : ℝ) * B := by ring
  have hm' : (m : ℝ) ≥ lam * μ₁ ^ 2 * (r : ℝ) * B := by
    simpa [N, B, hrearrange] using hm
  have htarget : B ≤ (m : ℝ) := le_trans hscale hm'
  simpa [B, N, mul_assoc] using htarget

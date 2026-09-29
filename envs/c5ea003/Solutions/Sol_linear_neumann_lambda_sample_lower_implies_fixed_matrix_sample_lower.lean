-- Prove2me | solution 1 for linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:31.961643+00:00
-- url     : https://prove2.me/submissions/d4a34a95-6502-46aa-ac6b-2a6231501ec8

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution
    (β lam : ℝ) (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ) :
    2 < β → 1 ≤ lam → 0 < n₁ → 0 < n₂ → 0 < r →
    1 ≤ μ₀ → 1 ≤ μ₁ →
    (m : ℝ) ≥
      lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
        (↑(max n₁ n₂)) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂))) →
    (m : ℝ) ≥
      β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
  intro _ hlam _ _ hr _ hμ₁ hm
  let N : ℝ := (max n₁ n₂ : ℝ)
  let B : ℝ := β * N * Real.log N
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hmax1 : 1 ≤ max (Real.sqrt μ₀) μ₁ := le_trans hμ₁ (le_max_right _ _)
  have hlam_nonneg : 0 ≤ lam := le_trans zero_le_one hlam
  have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  have h_lam_mu : 1 ≤ lam * μ₁ := by
    simpa using mul_le_mul hlam hμ₁ zero_le_one hlam_nonneg
  have h_lam_mu_nonneg : 0 ≤ lam * μ₁ := le_trans zero_le_one h_lam_mu
  have h_lam_mu_max : 1 ≤ lam * μ₁ * max (Real.sqrt μ₀) μ₁ := by
    simpa using mul_le_mul h_lam_mu hmax1 zero_le_one h_lam_mu_nonneg
  have h_lam_mu_max_nonneg :
      0 ≤ lam * μ₁ * max (Real.sqrt μ₀) μ₁ :=
    le_trans zero_le_one h_lam_mu_max
  have hfactor : 1 ≤ lam * μ₁ * max (Real.sqrt μ₀) μ₁ * (r : ℝ) := by
    simpa using mul_le_mul h_lam_mu_max hr1 zero_le_one h_lam_mu_max_nonneg
  have hlog_nonneg : 0 ≤ Real.log N := by
    have hN_ge_one : (1 : ℝ) ≤ N := by
      have hr_nat : 1 ≤ max n₁ n₂ := by omega
      dsimp [N]
      exact_mod_cast hr_nat
    exact Real.log_nonneg hN_ge_one
  have hB_nonneg : 0 ≤ B := by positivity
  have hscale : B ≤
      lam * μ₁ * max (Real.sqrt μ₀) μ₁ * (r : ℝ) * B :=
    by simpa using mul_le_mul_of_nonneg_right hfactor hB_nonneg
  have hrearrange :
      lam * μ₁ * max (Real.sqrt μ₀) μ₁ * N * (r : ℝ) *
          (β * Real.log N) =
        lam * μ₁ * max (Real.sqrt μ₀) μ₁ * (r : ℝ) * B := by
    ring
  have hm' : (m : ℝ) ≥
      lam * μ₁ * max (Real.sqrt μ₀) μ₁ * (r : ℝ) * B := by
    simpa [N, B, hrearrange] using hm
  have htarget : B ≤ (m : ℝ) := le_trans hscale hm'
  simpa [B, N, mul_assoc] using htarget

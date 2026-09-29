-- Prove2me | solution 2 for quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:26.017101+00:00
-- url     : https://prove2.me/submissions/85e8aaf6-2f87-489b-b5b8-dcf8001f9af4

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution
    (β lam : ℝ) (n₁ n₂ r m : ℕ) (μ₀ : ℝ) :
    2 < β → 1 ≤ lam → 0 < n₁ → 0 < n₂ → 0 < r →
    1 ≤ μ₀ →
    (m : ℝ) ≥
      lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
        (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
          (β * Real.log (↑(max n₁ n₂))) →
    (m : ℝ) ≥
      β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
  intro _ hlam _ _ hr hμ₀ hm
  let N : ℝ := (max n₁ n₂ : ℝ)
  let B : ℝ := β * N * Real.log N
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hμrpow : 1 ≤ Real.rpow μ₀ ((4 : ℝ) / 3) :=
    Real.one_le_rpow hμ₀ (by norm_num)
  have hrrpow : 1 ≤ Real.rpow (r : ℝ) ((4 : ℝ) / 3) :=
    Real.one_le_rpow hr1 (by norm_num)
  have hlam_nonneg : 0 ≤ lam := le_trans zero_le_one hlam
  have h_lam_mu : 1 ≤ lam * Real.rpow μ₀ ((4 : ℝ) / 3) := by
    simpa using mul_le_mul hlam hμrpow zero_le_one hlam_nonneg
  have h_lam_mu_nonneg :
      0 ≤ lam * Real.rpow μ₀ ((4 : ℝ) / 3) :=
    le_trans zero_le_one h_lam_mu
  have hfactor :
      1 ≤ lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
        Real.rpow (r : ℝ) ((4 : ℝ) / 3) := by
    simpa using mul_le_mul h_lam_mu hrrpow zero_le_one h_lam_mu_nonneg
  have hlog_nonneg : 0 ≤ Real.log N := by
    have hN_ge_one : (1 : ℝ) ≤ N := by
      have hr_nat : 1 ≤ max n₁ n₂ := by omega
      dsimp [N]
      exact_mod_cast hr_nat
    exact Real.log_nonneg hN_ge_one
  have hB_nonneg : 0 ≤ B := by positivity
  have hscale : B ≤
      lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
        Real.rpow (r : ℝ) ((4 : ℝ) / 3) * B :=
    by simpa using mul_le_mul_of_nonneg_right hfactor hB_nonneg
  have hrearrange :
      lam * Real.rpow μ₀ ((4 : ℝ) / 3) * N *
          Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
            (β * Real.log N) =
        lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
          Real.rpow (r : ℝ) ((4 : ℝ) / 3) * B := by
    ring
  have hm' : (m : ℝ) ≥
      lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
        Real.rpow (r : ℝ) ((4 : ℝ) / 3) * B := by
    have hmN :
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) * N *
            Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log N) := by
      simpa [N] using hm
    rw [hrearrange] at hmN
    exact hmN
  have htarget : B ≤ (m : ℝ) := le_trans hscale hm'
  simpa [B, N, mul_assoc] using htarget

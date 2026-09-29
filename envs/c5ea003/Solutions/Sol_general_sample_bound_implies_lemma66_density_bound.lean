-- Prove2me | solution 1 for general_sample_bound_implies_lemma66_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T10:38:40.258779+00:00
-- url     : https://prove2.me/submissions/692d8e5e-75c2-47fb-8277-372547470bb6

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

open MatrixCompletion

/-- Source: Candes--Recht 2008, PDF p. 6, Theorem 1.3/equation (1.9);
PDF p. 21, equation (4.19); and PDF p. 28, Lemma 6.6 immediately after
equation (6.15).

This is a purely scalar bridge: the `mu0 * N^(1/4)` branch in the global sample
complexity dominates the Lemma 6.6 density requirement because `N >= 1`. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
          ((8 : ℝ) / 3) * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) := by
  refine ⟨(8 : ℝ) / 3, by norm_num, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hμ₀ _hμ₁ hmLower
  let N : ℕ := max n₁ n₂
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_ge_one_nat : 1 ≤ N := Nat.succ_le_iff.mpr hN_pos_nat
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_one_nat
  have hN_nonneg : 0 ≤ (N : ℝ) := le_trans zero_le_one hN_ge_one
  have hN_rpow_ge_one :
      (1 : ℝ) ≤ Real.rpow (N : ℝ) ((1 : ℝ) / 4) := by
    exact Real.one_le_rpow hN_ge_one (by norm_num)
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hBranch :
      μ₀ ≤
        max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
          (μ₀ * Real.rpow (N : ℝ) ((1 : ℝ) / 4)) := by
    have hμ₀_le_rpow :
        μ₀ ≤ μ₀ * Real.rpow (N : ℝ) ((1 : ℝ) / 4) := by
      calc
        μ₀ = μ₀ * 1 := by ring
        _ ≤ μ₀ * Real.rpow (N : ℝ) ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hN_rpow_ge_one hμ₀_nonneg
    exact le_trans hμ₀_le_rpow (le_max_right _ _)
  have hC'_nonneg : 0 ≤ C' := le_trans (by norm_num : (0 : ℝ) ≤ (8 : ℝ) / 3) hC'
  have hMax_nonneg :
      0 ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
          (μ₀ * Real.rpow (N : ℝ) ((1 : ℝ) / 4)) :=
    le_trans hμ₀_nonneg hBranch
  have hCoeff :
      ((8 : ℝ) / 3) * μ₀ ≤
        C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
          (μ₀ * Real.rpow (N : ℝ) ((1 : ℝ) / 4)) := by
    exact mul_le_mul hC' hBranch hμ₀_nonneg hC'_nonneg
  have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
  have hβ_nonneg : 0 ≤ β := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg hN_ge_one
  have hTail_nonneg : 0 ≤ (N : ℝ) * (r : ℝ) * (β * Real.log (N : ℝ)) := by
    positivity
  have hTargetLe :
      ((8 : ℝ) / 3) * μ₀ * (N : ℝ) * (r : ℝ) *
          (β * Real.log (N : ℝ)) ≤
        C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (N : ℝ) ((1 : ℝ) / 4)) *
          (N : ℝ) * (r : ℝ) * (β * Real.log (N : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hCoeff hTail_nonneg
    nlinarith
  dsimp [N] at hTargetLe
  exact le_trans hTargetLe hmLower


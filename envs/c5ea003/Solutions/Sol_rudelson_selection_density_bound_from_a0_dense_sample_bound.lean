-- Prove2me | solution 1 for rudelson_selection_density_bound_from_a0_dense_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T04:19:30.931277+00:00
-- url     : https://prove2.me/submissions/161f1d6b-e6e4-489a-811f-341e3a0f8605

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem solution :
    ∀ (β μ₀ : ℝ) (n r m : ℕ),
      2 < β → 0 < n → 0 < r → 1 ≤ μ₀ →
      (m : ℝ) ≥ β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) →
      (m : ℝ) ≥ β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) := by
  intro β μ₀ n r m hβ hn _hr hμ₀ hm
  have hβ_nonneg : 0 ≤ β := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
  have hn_one_nat : 1 ≤ n := Nat.succ_le_of_lt hn
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg hn_one
  have hbase_nonneg :
      0 ≤ β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hβ_nonneg hn_nonneg) hr_nonneg)
      hlog_nonneg
  have hle :
      β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) ≤
        β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) := by
    calc
      β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ)
          = (β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ)) * 1 := by ring
      _ ≤ (β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ)) * μ₀ :=
          mul_le_mul_of_nonneg_left hμ₀ hbase_nonneg
      _ = β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) := by ring
  exact le_trans hle hm

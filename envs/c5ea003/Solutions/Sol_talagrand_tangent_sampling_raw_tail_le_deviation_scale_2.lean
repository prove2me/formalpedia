-- Prove2me | solution 2 for talagrand_tangent_sampling_raw_tail_le_deviation_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T18:58:07.889099+00:00
-- url     : https://prove2.me/submissions/fe3e1898-c07d-46f7-b59b-641cac4abb4f

import Definitions.Def_matrix_completion_talagrand
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (K : ℝ) :
    0 < K →
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ →
        K * Real.sqrt
            ((2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) *
              (β * Real.log (↑(max n₁ n₂)))) ≤
          tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m := by
  intro hK
  refine ⟨K * Real.sqrt 2, by positivity, ?_⟩
  intro β hβ n₁ n₂ r m μ₀ hn₁ hn₂ hr hμ₀
  let n : ℕ := max n₁ n₂
  let A : ℝ := (μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) / (m : ℝ)
  have hn : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg hn_real_ge_one
  have hβ_nonneg : 0 ≤ β :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hraw_arg :
      (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) *
          (β * Real.log (↑(max n₁ n₂))) =
        2 * A := by
    dsimp [A, n]
    ring
  unfold tangentSamplingDeviationScale
  rw [hraw_arg]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) A]
  simp [A, n, mul_assoc, mul_left_comm]

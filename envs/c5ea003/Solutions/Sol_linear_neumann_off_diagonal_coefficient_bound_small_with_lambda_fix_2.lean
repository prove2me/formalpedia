-- Prove2me | solution 2 for linear_neumann_off_diagonal_coefficient_bound_small_with_lambda_fix
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-06T14:05:03.566966+00:00
-- url     : https://prove2.me/submissions/a062996a-a94b-4fd3-9bb4-5a1541b41591

import Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_small_with_lambda

open MatrixCompletion

/-!
# `linear_neumann_off_diagonal_coefficient_bound_small_with_lambda_fix`

Target: `linear_neumann_off_diagonal_coefficient_bound_small_with_lambda_fix`
(`27731a86-25c8-41a0-9c75-e17d1f8dbb3d`, Open).

The target differs from the platform theorem
`linear_neumann_off_diagonal_coefficient_bound_small_with_lambda`
(`2bbc0f94-a5e1-4b51-983e-a5964fc70695`, **Proved**) in exactly one place: the
sample-size hypothesis carries `max μ₀ μ₁` where the proved theorem carries
`max (Real.sqrt μ₀) μ₁`.  Since `1 ≤ μ₀` gives `Real.sqrt μ₀ ≤ μ₀`, we have
`max (Real.sqrt μ₀) μ₁ ≤ max μ₀ μ₁`, and every other factor of the threshold
(`lam`, `μ₁`, `max n₁ n₂`, `r`, `β`, `Real.log (max n₁ n₂)`) is nonnegative under the
standing hypotheses.  Hence the target's hypothesis is the STRONGER one and implies
the proved theorem's, with an unchanged conclusion.

Single imported child, already `Proved`: a complete proof with no open dependency.
-/

theorem solution :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max μ₀ μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Ccoef, ccoef, hC, hc, H⟩ :=
    linear_neumann_off_diagonal_coefficient_bound_small_with_lambda
  refine ⟨Ccoef, ccoef, hC, hc, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hthr
  refine H β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 ?_
  -- the target's threshold dominates the proved theorem's threshold
  refine le_trans ?_ hthr
  have hN1 : (1 : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
    have : 1 ≤ max n₁ n₂ := le_max_of_le_left hn₁
    exact_mod_cast this
  have hlogN : 0 ≤ Real.log ((max n₁ n₂ : ℕ) : ℝ) := Real.log_nonneg hN1
  have hμ₀0 : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
  have hsqsq : Real.sqrt μ₀ ^ 2 = μ₀ := Real.sq_sqrt hμ₀0
  have hsn : (0 : ℝ) ≤ Real.sqrt μ₀ := Real.sqrt_nonneg μ₀
  have hone : (1 : ℝ) ≤ Real.sqrt μ₀ := by nlinarith [hsqsq, hsn, hμ₀]
  have hsq : Real.sqrt μ₀ ≤ μ₀ := by nlinarith [hsqsq, hsn, hone]
  have hmax : max (Real.sqrt μ₀) μ₁ ≤ max μ₀ μ₁ := max_le_max hsq le_rfl
  have hlam0 : (0 : ℝ) ≤ lam := le_trans zero_le_one hlam
  have hμ₁0 : (0 : ℝ) ≤ μ₁ := le_trans zero_le_one hμ₁
  have hN0 : (0 : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := le_trans zero_le_one hN1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hβ0 : (0 : ℝ) ≤ β := le_of_lt (lt_trans (by norm_num) hβ)
  gcongr

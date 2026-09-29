-- Prove2me | solution 3 for linear_neumann_correction_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T03:55:13.847721+00:00
-- url     : https://prove2.me/submissions/119b3abc-1976-4601-a4ac-d161d962a997

import Theorems.Thm_linear_neumann_diagonal_contribution_small_with_lambda
import Theorems.Thm_linear_neumann_off_diagonal_contribution_small_with_lambda
import Theorems.Thm_linear_neumann_correction_from_diagonal_off_diagonal_bounds
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF pp. 20 and 26-29, Lemma 4.5 and the proof
of Lemmas 6.4--6.7, especially equations (4.15), (6.8), (6.9), (6.13), and
(6.14).

Decompose Candes-Recht Lemma 4.5 into the diagonal and off-diagonal
contributions of (6.8). -/
theorem solution :
    ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 1
                ((C₁ * Real.rpow lam (-1)))) ≥
          1 - c₁ * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases linear_neumann_diagonal_contribution_small_with_lambda with
    ⟨Cdiag, cdiag, hCdiag, hcdiag, hDiag⟩
  rcases linear_neumann_off_diagonal_contribution_small_with_lambda with
    ⟨Coff, coff, hCoff, hcoff, hOff⟩
  refine ⟨Cdiag + Coff, cdiag + coff,
    add_pos hCdiag hCoff, add_pos hcdiag hcoff, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hDiagProb :=
    hDiag β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hOffProb :=
    hOff β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact linear_neumann_correction_from_diagonal_off_diagonal_bounds S
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Cdiag Coff cdiag coff β lam
    hpNonneg hpLeOne hcdiag hcoff hDiagProb hOffProb

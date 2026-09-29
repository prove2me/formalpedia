-- Prove2me | solution 1 for quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T15:51:06.062071+00:00
-- url     : https://prove2.me/submissions/d824215d-66a2-4863-9806-2115ffc94ac9

import Mathlib.Tactic
import Theorems.Thm_sign_matrix_spectral_norm_le_one
import Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_bound_min_dim

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF p. 24 rectangular-scale paragraph, PDF
p. 27 Lemma 6.4, and PDF p. 30 equation (6.21).  Lemma 6.4 is applied first
to the sign matrix and then to the resulting diagonal multiplier.  The source
paragraph after (6.2)--(6.4) says that the rectangular case replaces `n` by
`min(n₁,n₂)`. -/
theorem solution :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        spectralNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2) := by
  rcases tangent_diagonal_multiplier_spectral_norm_bound_min_dim with
    ⟨Cdiag, hCdiag_pos, hdiag⟩
  refine ⟨Cdiag ^ 2, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  let a : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂))
  have hfactor_nonneg : 0 ≤ Cdiag * a := by
    dsimp [a]
    positivity
  have hlinear :
      spectralNorm (linearNeumannDiagonalBaseMatrix S) ≤ Cdiag * a := by
    have hraw := hdiag n₁ n₂ r M μ₀ S (signMatrix S) hn₁ hn₂ hr hμ₀ hA0
    have hsign := sign_matrix_spectral_norm_le_one S
    calc
      spectralNorm (linearNeumannDiagonalBaseMatrix S)
          = spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) := by
              rfl
      _ ≤ Cdiag * a * spectralNorm (signMatrix S) := by
              simpa [a] using hraw
      _ ≤ Cdiag * a * 1 := by
              exact mul_le_mul_of_nonneg_left hsign hfactor_nonneg
      _ = Cdiag * a := by ring
  have hquad_raw := hdiag n₁ n₂ r M μ₀ S (linearNeumannDiagonalBaseMatrix S)
    hn₁ hn₂ hr hμ₀ hA0
  calc
    spectralNorm (quadraticNeumannAllEqualBaseMatrix S)
        = spectralNorm (tangentDiagonalMultiplier S (linearNeumannDiagonalBaseMatrix S)) := by
            rfl
    _ ≤ Cdiag * a * spectralNorm (linearNeumannDiagonalBaseMatrix S) := by
            simpa [a] using hquad_raw
    _ ≤ Cdiag * a * (Cdiag * a) := by
            exact mul_le_mul_of_nonneg_left hlinear hfactor_nonneg
    _ = Cdiag ^ 2 * (a ^ 2) := by ring
    _ = Cdiag ^ 2 * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2) := by rfl

-- Prove2me | solution 1 for tangent_diagonal_multiplier_spectral_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T17:29:25.649962+00:00
-- url     : https://prove2.me/submissions/14297858-1151-4f58-a594-03c855a574bc

import Theorems.Thm_a0_singular_coordinate_energy_bounds
import Theorems.Thm_svd_singular_coordinate_energy_le_one
import Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies

open MatrixCompletion

open scoped Classical BigOperators

/-- Source: Candes-Recht 2008, PDF p. 27, Lemma 6.4, equations
(6.10)--(6.11), together with the rectangular-scale convention stated on PDF
p. 24 after estimates (6.2)--(6.4).  Lemma 6.4 bounds the diagonal
tangent-kernel multiplier by writing it as
`Λ_U X (I - Λ_V) + X Λ_V`; this sketch separates the paper's A0 coordinate
energy inputs and the orthonormality/Bessel inputs from that core multiplier
argument. -/
theorem solution :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        spectralNorm (tangentDiagonalMultiplier S X) ≤
          Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm X := by
  rcases tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies with
    ⟨Cdiag, hCdiag_pos, hdiag⟩
  refine ⟨Cdiag, hCdiag_pos, ?_⟩
  intro n₁ n₂ r M μ₀ S X hn₁ hn₂ hr hμ₀ hA0
  have hEnergy := a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0
  have hOne := svd_singular_coordinate_energy_le_one S
  exact hdiag n₁ n₂ r M μ₀ S X hn₁ hn₂ hr hμ₀
    hEnergy.1 hEnergy.2 hOne.1 hOne.2

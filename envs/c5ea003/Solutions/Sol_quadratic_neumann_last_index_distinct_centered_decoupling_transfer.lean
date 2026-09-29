-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_decoupling_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T02:02:24.949393+00:00
-- url     : https://prove2.me/submissions/2200ff4b-8742-4ce7-8938-d70845e27e04

import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_decoupling_transfer
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_pair_decoupling_tail_bound
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_original_tail_from_diagonal_decoupled_tail

open MatrixCompletion

/-- Prove the centered `ω₁ = ω₂ ≠ ω₃` decoupling transfer from the
threshold-form pair-decoupling tail bound and the diagonal-coupling transfer. -/
theorem solution :
    ∃ Cdecouple cdecouple : ℝ, 0 < Cdecouple ∧ 0 < cdecouple ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r) (p Cdec cdec β lam : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliPairEventProb p
            (fun Omega1 Omega3 =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega3 S p) ≤
                Cdec * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) ≤
                (Cdecouple * Cdec) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - (cdecouple * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_last_index_distinct_centered_pair_decoupling_tail_bound with
    ⟨K, L, hK, hL, hPair⟩
  refine ⟨K, L, hK, hL, ?_⟩
  intro n₁ n₂ r M S p Cdec cdec β lam hp0 hp1 hCdec hcdec hDecoupled
  have hDiagonal :=
    hPair S p Cdec cdec
      (Real.rpow (↑(max n₁ n₂)) (-β))
      (Real.rpow lam (-((3 : ℝ) / 2)))
      hp0 hp1 hCdec hcdec hDecoupled
  exact
    quadratic_neumann_last_index_distinct_centered_original_tail_from_diagonal_decoupled_tail
      S p ((K * Cdec) * Real.rpow lam (-((3 : ℝ) / 2)))
      (1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β))
      hp0 hp1 hDiagonal


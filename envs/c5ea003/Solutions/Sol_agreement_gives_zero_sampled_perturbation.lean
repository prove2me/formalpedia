-- Prove2me | solution 1 for agreement_gives_zero_sampled_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:48.471637+00:00
-- url     : https://prove2.me/submissions/3d7c56ea-b236-4e1c-8233-6f46afdebc2b

import Theorems.Thm_agreement_gives_zero_sampled_perturbation

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂))
    (X M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    AgreesOn Omega X M →
    samplingProjection Omega (X - M) = 0 := by
  intro hagree
  ext i j
  by_cases hmem : (i, j) ∈ Omega
  · have hXM : X i j = M i j := hagree (i, j) hmem
    simp [samplingProjection, hmem, hXM]
  · simp [samplingProjection, hmem]


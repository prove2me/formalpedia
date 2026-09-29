-- Prove2me | solution 1 for linear_neumann_off_diagonal_pair_decoupling_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T05:00:29.489188+00:00
-- url     : https://prove2.me/submissions/c79c2d40-af2f-4795-93e3-e03bd0deb231

import Theorems.Thm_bernoulli_pair_decoupling_spectral_tail_bound_offdiag

open MatrixCompletion
open scoped BigOperators Classical

/-- Reduction of `linear_neumann_off_diagonal_pair_decoupling_tail_bound` onto
the corrected, paper-faithful order-2 de la Peña core
`bernoulli_pair_decoupling_spectral_tail_bound_offdiag`.  The concrete kernel
`linearNeumannOffDiagonalDecoupledContribution` is literally the off-diagonal
bilinear U-statistic the paper requires (`if w1 = w2 then 0 else …`), so the
tetrahedral representation hypothesis is discharged by exhibiting the coefficient
family `a w1 w2 = (p⁻¹)² • (sign·kernel) • coord`.

de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816, Thm 1 (k=2). -/
theorem solution :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliPairEventProb p
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S p) ≤
                Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega Omega S p) ≤
                (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  obtain ⟨K, L, hK, hL, hcore⟩ :=
    bernoulli_pair_decoupling_spectral_tail_bound_offdiag
  refine ⟨K, L, hK, hL, ?_⟩
  intro n₁ n₂ r M S p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec hhyp
  refine hcore
    (fun Omega1 Omega2 =>
      linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S p)
    p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec ?_ hhyp
  -- discharge the off-diagonal representation hypothesis
  refine ⟨fun w1 w2 =>
    (p⁻¹) ^ 2 •
      (signMatrix S w2.1 w2.2 *
        tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
        coordinateMatrix w1.1 w1.2, ?_⟩
  intro Omega1 Omega2
  show linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S p = _
  rw [linearNeumannOffDiagonalDecoupledContribution]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w1 _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w2 _ => ?_)
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    simp only [smul_smul]
    congr 1
    ring

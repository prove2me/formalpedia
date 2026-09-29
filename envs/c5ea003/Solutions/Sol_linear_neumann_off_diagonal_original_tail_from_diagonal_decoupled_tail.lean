-- Prove2me | solution 1 for linear_neumann_off_diagonal_original_tail_from_diagonal_decoupled_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T01:51:46.50823+00:00
-- url     : https://prove2.me/submissions/439a2952-4196-4f4d-98dd-8a66ad413194

import Theorems.Thm_linear_neumann_off_diagonal_original_tail_from_diagonal_decoupled_tail
import Theorems.Thm_linear_neumann_off_diagonal_diagonal_decoupled_equals_original
import Theorems.Thm_bernoulli_event_probability_mono

open MatrixCompletion

/-- Prove the original-tail transfer for the off-diagonal first Neumann term
from the diagonal-coupling identity and event monotonicity. -/
theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p bound lower : ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm
            (linearNeumannOffDiagonalDecoupledContribution Omega Omega S p) ≤
            bound) ≥ lower →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
            bound) ≥ lower := by
  intro hp0 hp1 hDiagProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (linearNeumannOffDiagonalDecoupledContribution Omega Omega S p) ≤
              bound) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
              bound) :=
    bernoulli_event_probability_mono p
      (fun Omega =>
        spectralNorm
          (linearNeumannOffDiagonalDecoupledContribution Omega Omega S p) ≤
          bound)
      (fun Omega =>
        spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
          bound)
      hp0 hp1
      (by
        intro Omega hOmega
        simpa [linear_neumann_off_diagonal_diagonal_decoupled_equals_original
          Omega S p] using hOmega)
  linarith


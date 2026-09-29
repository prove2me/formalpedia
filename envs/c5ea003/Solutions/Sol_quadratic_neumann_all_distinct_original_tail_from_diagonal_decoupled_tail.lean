-- Prove2me | solution 1 for quadratic_neumann_all_distinct_original_tail_from_diagonal_decoupled_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T01:54:24.199913+00:00
-- url     : https://prove2.me/submissions/860fa6ee-953f-473c-a91e-b3c35c500986

import Theorems.Thm_quadratic_neumann_all_distinct_original_tail_from_diagonal_decoupled_tail
import Theorems.Thm_quadratic_neumann_all_distinct_diagonal_decoupled_equals_original
import Theorems.Thm_bernoulli_event_probability_mono

open MatrixCompletion

/-- Prove the original-tail transfer by monotonicity of Bernoulli probabilities
and the deterministic identity between the original all-distinct term and the
diagonal coupling of the triple-decoupled model. -/
theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p bound lower : ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm
            (quadraticNeumannAllDistinctDecoupledContribution
              Omega Omega Omega S p) ≤ bound) ≥ lower →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
            bound) ≥ lower := by
  intro hp0 hp1 hDiagProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannAllDistinctDecoupledContribution
                Omega Omega Omega S p) ≤ bound) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
              bound) :=
    bernoulli_event_probability_mono p
      (fun Omega =>
        spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution
            Omega Omega Omega S p) ≤ bound)
      (fun Omega =>
        spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
          bound)
      hp0 hp1
      (by
        intro Omega hOmega
        simpa [quadratic_neumann_all_distinct_diagonal_decoupled_equals_original
          Omega S p] using hOmega)
  linarith


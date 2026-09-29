-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_pair_decoupling_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T05:01:01.714044+00:00
-- url     : https://prove2.me/submissions/74c7e5af-ab54-4646-b0fd-5fca13d1b27b

import Theorems.Thm_bernoulli_pair_decoupling_spectral_tail_bound_offdiag

open MatrixCompletion
open scoped BigOperators Classical

/-- Reduction of
`quadratic_neumann_last_index_distinct_centered_pair_decoupling_tail_bound`
onto the corrected, paper-faithful order-2 de la Peña core
`bernoulli_pair_decoupling_spectral_tail_bound_offdiag`.  Off-diagonal kernel
`quadraticNeumannLastIndexDistinctCenteredDecoupledContribution`; coefficient
family `a w1 w3 = (p⁻¹)³ • ((1-2p)·sign_{w3}·kernel(w3,w1)·kernel(w1,w1)) • coord`.

de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816, Thm 1 (k=2). -/
theorem solution :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliPairEventProb p
            (fun Omega1 Omega3 =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega3 S p) ≤
                Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega Omega S p) ≤
                (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  obtain ⟨K, L, hK, hL, hcore⟩ :=
    bernoulli_pair_decoupling_spectral_tail_bound_offdiag
  refine ⟨K, L, hK, hL, ?_⟩
  intro n₁ n₂ r M S p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec hhyp
  refine hcore
    (fun Omega1 Omega3 =>
      quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
        Omega1 Omega3 S p)
    p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec ?_ hhyp
  refine ⟨fun w1 w3 =>
    (p⁻¹) ^ 3 •
      ((1 - 2 * p) *
        signMatrix S w3.1 w3.2 *
          tangentCoordinateKernel S w3.1 w3.2 w1.1 w1.2 *
            tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2) •
        coordinateMatrix w1.1 w1.2, ?_⟩
  intro Omega1 Omega3
  show quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
        Omega1 Omega3 S p = _
  rw [quadraticNeumannLastIndexDistinctCenteredDecoupledContribution]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w1 _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w3 _ => ?_)
  by_cases h : w1 = w3
  · simp [h]
  · simp only [h, if_false]
    simp only [smul_smul]
    congr 1
    ring

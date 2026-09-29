-- Prove2me | solution 1 for quadratic_neumann_all_distinct_triple_decoupling_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T05:01:02.019421+00:00
-- url     : https://prove2.me/submissions/bee81cba-4126-4753-8d1d-829ba8c1d381

import Theorems.Thm_bernoulli_triple_decoupling_spectral_tail_bound_offdiag

open MatrixCompletion
open scoped BigOperators Classical

/-- Reduction of
`quadratic_neumann_all_distinct_triple_decoupling_tail_bound` onto the corrected,
paper-faithful order-3 de la Peña core
`bernoulli_triple_decoupling_spectral_tail_bound_offdiag`.  The kernel
`quadraticNeumannAllDistinctDecoupledContribution` is the all-distinct trilinear
U-statistic (`if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then 0 else …`) the paper requires;
the tetrahedral representation hypothesis is discharged with the coefficient
family `a w1 w2 w3 = (p⁻¹)³ • (sign_{w3}·kernel(w3,w2)·kernel(w2,w1)) • coord`.

de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816, Thm 1 (k=3). -/
theorem solution :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliTripleEventProb p
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S p) ≤
                Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega Omega Omega S p) ≤
                (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  obtain ⟨K, L, hK, hL, hcore⟩ :=
    bernoulli_triple_decoupling_spectral_tail_bound_offdiag
  refine ⟨K, L, hK, hL, ?_⟩
  intro n₁ n₂ r M S p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec hhyp
  refine hcore
    (fun Omega1 Omega2 Omega3 =>
      quadraticNeumannAllDistinctDecoupledContribution
        Omega1 Omega2 Omega3 S p)
    p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec ?_ hhyp
  refine ⟨fun w1 w2 w3 =>
    (p⁻¹) ^ 3 •
      (signMatrix S w3.1 w3.2 *
        tangentCoordinateKernel S w3.1 w3.2 w2.1 w2.2 *
          tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
        coordinateMatrix w1.1 w1.2, ?_⟩
  intro Omega1 Omega2 Omega3
  show quadraticNeumannAllDistinctDecoupledContribution
        Omega1 Omega2 Omega3 S p = _
  rw [quadraticNeumannAllDistinctDecoupledContribution]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w1 _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w2 _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun w3 _ => ?_)
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    simp only [smul_smul]
    congr 1
    ring

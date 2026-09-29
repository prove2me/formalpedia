-- Prove2me | Theorems.Thm_bernoulli_triple_decoupling_spectral_tail_bound_offdiag
-- name    : bernoulli_triple_decoupling_spectral_tail_bound_offdiag
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T05:00:07.245933+00:00
-- url     : https://prove2.me/theorems/55f0c9c3-66c3-42c0-b9ee-a16246647083
-- statement:
--   Faithful (corrected) order-3 de la Peña–Montgomery-Smith triple decoupling tail bound for the spectral norm over the Bernoulli powerset sampling model, carrying the EXACT all-distinct (tetrahedral) hypothesis the theorem requires. There exist universal constants $K,L>0$ (the order-3 constant $C_3$) such that for every trilinear kernel $G$ that admits an **all-distinct trilinear representation** $G(\Omega_1,\Omega_2,\Omega_3)=\sum_{w_1,w_2,w_3\text{ distinct}}(\xi_{w_1}(\Omega_1)\xi_{w_2}(\Omega_2)\xi_{w_3}(\Omega_3))\,a_{w_1 w_2 w_3}$, the tail of the diagonal (coupled) statistic $G(\Omega,\Omega,\Omega)$ is controlled by the tail of the decoupled statistic $G(\Omega_1,\Omega_2,\Omega_3)$ under the independent-triple measure, with the same $K\,C_{dec}$ threshold and $L\,c_{dec}$ failure scaling. This is the order-3 case of de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), Theorem 1, with the tetrahedral constraint $i_1\neq i_2\neq i_3$ (all distinct). NOTE: replaces the under-specified node bernoulli_triple_decoupling_spectral_tail_bound (f90b8aa4), which omitted the all-distinct hypothesis.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

theorem bernoulli_triple_decoupling_spectral_tail_bound_offdiag :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ : ℕ}
        (G : Finset (Fin n₁ × Fin n₂) →
             Finset (Fin n₁ × Fin n₂) →
             Finset (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        -- All-distinct (tetrahedral) trilinear representation hypothesis.
        (∃ a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
               (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂,
            ∀ Omega1 Omega2 Omega3 : Finset (Fin n₁ × Fin n₂),
              G Omega1 Omega2 Omega3 =
                ∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                  ∑ w3 : Fin n₁ × Fin n₂,
                  (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then
                      (0 : RealMatrix n₁ n₂)
                   else
                     (centeredIndicator Omega1 p w1.1 w1.2 *
                       centeredIndicator Omega2 p w2.1 w2.2 *
                       centeredIndicator Omega3 p w3.1 w3.2) • a w1 w2 w3)) →
        bernoulliTripleEventProb p
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm (G Omega1 Omega2 Omega3) ≤ Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (G Omega Omega Omega) ≤ (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  sorry

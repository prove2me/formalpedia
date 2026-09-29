-- Prove2me | Theorems.Thm_bernoulli_pair_decoupling_spectral_tail_bound_offdiag
-- name    : bernoulli_pair_decoupling_spectral_tail_bound_offdiag
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T04:57:21.666318+00:00
-- url     : https://prove2.me/theorems/f92f825a-6e03-4c96-892e-54db25c40c9f
-- statement:
--   Faithful (corrected) order-2 de la Peña–Montgomery-Smith pair decoupling tail bound for the spectral norm over the Bernoulli powerset sampling model, carrying the EXACT tetrahedral / off-diagonal hypothesis the theorem requires. There exist universal constants $K,L>0$ (the order-2 decoupling constant $C_2$) such that for every matrix-valued bilinear sampling kernel $G$ that admits an **off-diagonal bilinear representation** $G(\Omega_1,\Omega_2)=\sum_{w_1\neq w_2}(\xi_{w_1}(\Omega_1)\,\xi_{w_2}(\Omega_2))\,a_{w_1 w_2}$ (centered indicators $\xi$, the $w_1\neq w_2$ guard being de la Peña–Montgomery-Smith's tetrahedral constraint $i_1\neq i_2$), the tail of the **diagonal** (coupled) statistic $G(\Omega,\Omega)$ under the single-sample measure is controlled by the tail of the **decoupled** statistic $G(\Omega_1,\Omega_2)$ under the independent-pair measure: if $\Pr[\,\|G(\Omega_1,\Omega_2)\|\le C_{dec}\,t\,]\ge 1-c_{dec}f$ then $\Pr[\,\|G(\Omega,\Omega)\|\le K\,C_{dec}\,t\,]\ge 1-L\,c_{dec}f$. This is the order-2 case of de la Peña–Montgomery-Smith, *Decoupling Inequalities for the Tail Probabilities of Multivariate U-Statistics*, Ann. Probab. 23 (1995), no. 2, 806–816 (arXiv:math/9309211), Theorem 1: $P(\|S\|\ge t)\le C_k P(C_k\|S'\|\ge t)$, summed over the tetrahedral index set $i_1\neq i_2$. NOTE: this replaces the earlier under-specified node bernoulli_pair_decoupling_spectral_tail_bound (3b904726), which dropped the tetrahedral hypothesis and quantified over an arbitrary $G$; decoupling is FALSE for kernels with a diagonal part, so the off-diagonal representation hypothesis is essential.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

theorem bernoulli_pair_decoupling_spectral_tail_bound_offdiag :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ : ℕ}
        (G : Finset (Fin n₁ × Fin n₂) →
             Finset (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        -- Tetrahedral / off-diagonal representation hypothesis (de la Peña–
        -- Montgomery-Smith Theorem 1: the U-statistic is summed over the
        -- off-diagonal index set `w₁ ≠ w₂`, with `Ω₁, Ω₂` the independent
        -- copies and `a` the index-coefficient family).
        (∃ a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂,
            ∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
              G Omega1 Omega2 =
                ∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                  (if w1 = w2 then (0 : RealMatrix n₁ n₂)
                   else
                     (centeredIndicator Omega1 p w1.1 w1.2 *
                       centeredIndicator Omega2 p w2.1 w2.2) • a w1 w2)) →
        bernoulliPairEventProb p
            (fun Omega1 Omega2 =>
              spectralNorm (G Omega1 Omega2) ≤ Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (G Omega Omega) ≤ (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  sorry

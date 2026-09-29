-- Prove2me | Theorems.Thm_mme_CW_base_same_marginals_unique
-- name    : mme_CW_base_same_marginals_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:26:41.350106+00:00
-- url     : https://prove2.me/theorems/4a4ba823-c0a5-4744-b383-4919a054c5c2
-- title:
--   CW base weights are determined by their three marginals
-- statement:
--   Let $S$ be the six ordered CW base grades $(0,0,2),(0,1,1),(0,2,0),(1,0,1),(1,1,0),(2,0,0)$. For two real weight functions $\rho,\alpha:S\to\mathbb R$, suppose their marginal masses agree at each value of each of the three coordinates. Then
--
--   $$\rho=\alpha,\qquad H_2(\rho)=H_2(\alpha).$$
--
--   No normalization or nonnegativity hypothesis is needed for the weight identity. In particular, for probability distributions supported on the splitting cells of any CW square component, the same-marginal feasible set is a singleton after extension by zero to $S$. Its maximum-entropy loss is therefore exactly zero; numerical entropy maximization at this square-input layer is unnecessary.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Section3.4, printed p.19 (six CW base grades), Section3.5 (square splitting as pairs of base grades), and Section8.1 (lower-level symmetric-hashing values). This is the elementary marginal-rigidity consequence of the displayed six-cell support, not a separately numbered theorem in the paper.

import Definitions.Def_mme_modern_entropy_data

set_option autoImplicit false

open BigOperators

theorem mme_CW_base_same_marginals_unique (rho alpha : Fin 6 → ℝ)
    (hX : ∀ k : Fin 3,
      mme_modern_marginal (![0, 0, 0, 1, 1, 2] : Fin 6 → Fin 3) rho k =
        mme_modern_marginal (![0, 0, 0, 1, 1, 2] : Fin 6 → Fin 3) alpha k)
    (hY : ∀ k : Fin 3,
      mme_modern_marginal (![0, 1, 2, 0, 1, 0] : Fin 6 → Fin 3) rho k =
        mme_modern_marginal (![0, 1, 2, 0, 1, 0] : Fin 6 → Fin 3) alpha k)
    (hZ : ∀ k : Fin 3,
      mme_modern_marginal (![2, 1, 0, 1, 0, 0] : Fin 6 → Fin 3) rho k =
        mme_modern_marginal (![2, 1, 0, 1, 0, 0] : Fin 6 → Fin 3) alpha k) :
    rho = alpha ∧ mme_modern_entropyBits rho = mme_modern_entropyBits alpha := by sorry

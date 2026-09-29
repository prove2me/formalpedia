-- Prove2me | Theorems.Thm_dlp_eq4_four_corner_randomization_k2
-- name    : dlp_eq4_four_corner_randomization_k2
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T05:21:19.347462+00:00
-- url     : https://prove2.me/theorems/f4b0c019-10e5-4f8d-9ae7-859c0a219105
-- statement:
--   **de la Peña–Montgomery-Smith eq (4), order $k=2$** (Ann. Probab. 23 (1995), 806–816; arXiv:math/9309211, §4). For independent symmetric Bernoulli signs $\sigma_1,\sigma_2\in\{\pm1\}$ at the two distinct indices $i_1\neq i_2$, and any Banach-valued bilinear coefficient family $f:\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to V$ (where $f\,j_1\,j_2$ stands for $f_{i_1 i_2}(X^{(j_1)}_{i_1},X^{(j_2)}_{i_2})$), the $\sigma$-randomized decoupled term expands as the four-corner sign-weighted average over the i.i.d. copies: $$4\,f(Z^{(l_1)},Z^{(l_2)})=\sum_{j_1,j_2\in\{1,2\}}(1+s(j_1,l_1)\sigma_1)(1+s(j_2,l_2)\sigma_2)\,f(X^{(j_1)},X^{(j_2)}),$$ where $Z^{(l)}=X^{(\mathrm{copyPerm}\,\sigma\,l)}$ and $s=\mathrm{dlpCornerSign}$ is the agreement sign ($+1$ if the copy superscript equals the target superscript, else $-1$). This is the $k=2$ specialisation of eq (4): the product of two single-slot $2\,g(Z^{(l)})=\sum_j(1+s(j,l)\sigma)\,g^{(j)}$ identities, each verified by case analysis on $\sigma\in\{\pm1\}$ and the target $l$.
-- source:
--   de la Peña & Montgomery-Smith, Decoupling inequalities for the tail probabilities of multivariate U-statistics, Ann. Probab. 23 (1995), 806–816; arXiv:math/9309211, §4, eq (4).

import Definitions.Def_dlp_sigma_randomization

open MatrixCompletion
open scoped BigOperators Classical

theorem dlp_eq4_four_corner_randomization_k2
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (σ₁ σ₂ : ℝ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → V) :
    (4 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2,
          ((1 + dlpCornerSign j₁ l₁ * σ₁) * (1 + dlpCornerSign j₂ l₂ * σ₂))
            • f j₁ j₂ := by sorry

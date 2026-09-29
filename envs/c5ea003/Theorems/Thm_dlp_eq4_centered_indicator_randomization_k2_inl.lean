-- Prove2me | Theorems.Thm_dlp_eq4_centered_indicator_randomization_k2_inl
-- name    : dlp_eq4_centered_indicator_randomization_k2_inl
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T17:06:30.577056+00:00
-- url     : https://prove2.me/theorems/ee423e2b-db37-4a3e-85ae-3239dae34cef
-- statement:
--   Concrete matrix-model instantiation of the de la Peña–Montgomery-Smith σ-randomization identity, equation (4) of Section 4 of *Decoupling Inequalities for the Tail Probabilities of Multivariate U-Statistics* (Ann. Probab. 23 (1995) 806–816, arXiv:math/9309211), specialized to order $k=2$ on the Bernoulli powerset sampling model. For the scalar two-copy product of centered indicators $\xi_{w_1}(\Omega^{(j_1)})\,\xi_{w_2}(\Omega^{(j_2)})$ with $\xi=$ `centeredIndicator`, reading the $j$-th of the two i.i.d. observation copies ($X^{(1)}=\Omega_1$ at $j=0$, $X^{(2)}=\Omega_2$ at $j=1$, inlined as `if j = 0 then Ω₁ else Ω₂`), and the σ-permuted decoupled $Z$-copies $Z^{(l)}=X^{(\mathrm{copyPerm}\,\sigma\,l)}$, the four-corner identity holds: $4\,\xi_{w_1}(Z^{(l_1)})\,\xi_{w_2}(Z^{(l_2)}) = \sum_{j_1,j_2\in\{1,2\}}(1+\mathrm{cornerSign}(j_1,l_1)\sigma_1)(1+\mathrm{cornerSign}(j_2,l_2)\sigma_2)\,\xi_{w_1}(X^{(j_1)})\,\xi_{w_2}(X^{(j_2)})$. Pure algebra: a direct specialization (to $V=\mathbb R$ and the centered-indicator statistic) of the already-proved abstract four-corner randomization `dlp_eq4_four_corner_randomization_k2`. Supplies the σ-randomization (eq 4) step of the de la Peña pair-decoupling forward bound `bernoulli_pair_decoupling_spectral_tail_bound_offdiag` on the concrete model. (Suffix `_inl`: copy-selector fully inlined into the statement so the whole declaration is a single theorem.)
-- source:
--   de la Peña, V. H. and Montgomery-Smith, S. J. (1995). Decoupling inequalities for the tail probabilities of multivariate U-statistics. Ann. Probab. 23(2), 806-816. arXiv:math/9309211, Section 4, equation (4).

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_dlp_sigma_randomization
open MatrixCompletion
open scoped BigOperators Classical

theorem dlp_eq4_centered_indicator_randomization_k2_inl
    {n1 n2 : Nat}
    (Omega1 Omega2 : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (w1 w2 : Fin n1 × Fin n2)
    (sigma1 sigma2 : ℝ) (hs1 : sigma1 = 1 ∨ sigma1 = -1) (hs2 : sigma2 = 1 ∨ sigma2 = -1)
    (l1 l2 : Fin 2) :
    (4 : ℝ) *
        (centeredIndicator (if dlpCopyPerm sigma1 l1 = 0 then Omega1 else Omega2) p w1.1 w1.2 *
          centeredIndicator (if dlpCopyPerm sigma2 l2 = 0 then Omega1 else Omega2) p w2.1 w2.2)
      = ∑ j1 : Fin 2, ∑ j2 : Fin 2,
          ((1 + dlpCornerSign j1 l1 * sigma1) * (1 + dlpCornerSign j2 l2 * sigma2)) *
            (centeredIndicator (if j1 = 0 then Omega1 else Omega2) p w1.1 w1.2 *
              centeredIndicator (if j2 = 0 then Omega1 else Omega2) p w2.1 w2.2) := by sorry

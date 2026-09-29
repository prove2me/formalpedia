-- Prove2me | Theorems.Thm_dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl
-- name    : dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T17:06:56.176857+00:00
-- url     : https://prove2.me/theorems/7188b43f-b2aa-45e7-b7b5-843d59cf4f6c
-- statement:
--   Conditional Lemma 2 (equation (6) of Section 4) of de la Peña–Montgomery-Smith, *Decoupling Inequalities for the Tail Probabilities of Multivariate U-Statistics* (Ann. Probab. 23 (1995) 806–816, arXiv:math/9309211), instantiated at order $k=2$ for the concrete matrix-valued off-diagonal $\sigma$-sign chaos on the symmetric Rademacher fiber. Let $\Xi(\varepsilon)=\sum_{w_1\neq w_2}(\varepsilon_{w_1}\varepsilon_{w_2})\,a_{w_1 w_2}$ be the tetrahedral bilinear sign chaos with matrix coefficients $a_{w_1 w_2}\in\mathbb R^{n_1\times n_2}$ (inlined as the guarded double sum), and let $T$ be a conditioning matrix. Following de la Peña's Proposition 1, fix a dual unit pair $(x,y)$ ($\|x\|,\|y\|\le 1$) norming $T$, i.e. $\langle(\mathrm{toEuclideanLin}\,T)x,y\rangle=\|T\|$ (spectral norm). Then, provided the scalar dual image $F(\varepsilon)=\langle(\mathrm{toEuclideanLin}\,\Xi(\varepsilon))x,y\rangle$ is mean-zero with strictly positive variance (the standing Proposition 1 non-degeneracy hypotheses), the $\sigma$-mass of the survival event is bounded below: $\Pr_\sigma(\|T\|\le\|T+\Xi(\varepsilon)\|)\ge 1/324$. The constant $1/324=1/(4\cdot 81)$ comes from Bonami's degree-2 hypercontractivity ($E[F^4]\le 81(E[F^2])^2$) feeding the Paley–Zygmund positivity $\Pr(F\ge 0)\ge 1/(4K)$, with the norming-functional containment $\{F\ge 0\}\subseteq\{\|T\|\le\|T+\Xi\|\}$. This is the genuine conditional-positivity content (eq 6) of the de la Peña pair-decoupling forward bound `bernoulli_pair_decoupling_spectral_tail_bound_offdiag`. (Suffix `_inl`: matrix chaos fully inlined so the declaration is a single theorem.)
-- source:
--   de la Peña, V. H. and Montgomery-Smith, S. J. (1995). Decoupling inequalities for the tail probabilities of multivariate U-statistics. Ann. Probab. 23(2), 806-816. arXiv:math/9309211, Section 4, equation (6), Lemma 2 and Proposition 1; Bonami (1970) Ann. Inst. Fourier 20, 335-402.

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    (hmean :
      rademacherExpectation
        (fun eps => ⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)) xv, yv⟫_ℝ) = 0)
    (hvar :
      0 < rademacherExpectation
        (fun eps => (⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)) xv, yv⟫_ℝ) ^ 2)) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by sorry

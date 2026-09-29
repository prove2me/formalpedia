-- Prove2me | Theorems.Thm_tangent_projection_self_adjoint
-- name    : tangent_projection_self_adjoint
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-24T03:11:54.782989+00:00
-- url     : https://prove2.me/theorems/e28b61b3-3c61-4b1e-a896-c7b9c2ce0e94
-- statement:
--   The tangent-space projection $P_T = P_{\text{left}} + P_{\text{right}} - P_{\text{two-sided}}$ (built from the singular subspaces of an SVD of $M$) is **self-adjoint** for the Frobenius inner product: for all real $n_1\times n_2$ matrices $A,B$, $\langle P_T A, B\rangle_F = \langle A, P_T B\rangle_F$. Each constituent projection has a symmetric kernel ($\sum_k u_{ki}u_{ka}$ on the left, $\sum_\ell v_{\ell b}v_{\ell j}$ on the right), and the two-sided projection equals the composition $P_{\text{left}}\circ P_{\text{right}} = P_{\text{right}}\circ P_{\text{left}}$, so it is self-adjoint as a composition of self-adjoint maps. This is the basic orthogonal-projection property underlying the Cand\`es--Recht tangent-space analysis (arXiv:0805.4471 §3--§4.2): it gives the resolution of identity $X=\sum_{ab}\langle P_T(e_ae_b^*),X\rangle_F\,P_T(e_ae_b^*)$ for $X\in T$ and the rank-one frame representation of the sampling fluctuation $P_TP_\Omega P_T - pP_T$ used in the Rudelson selection lemma (Rudelson 1999, J. Funct. Anal. 164, Thm 1).
-- source:
--   Candès–Recht arXiv:0805.4471 §3–§4.2; Rudelson 1999 J. Funct. Anal. 164

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Matrix

theorem tangent_projection_self_adjoint
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    matrixInner (tangentProjection S A) B
      = matrixInner A (tangentProjection S B) := by sorry

-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_K_decomposition
-- name    : MatrixCompletion.NoSpuriousMin.K_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:12:25.237835+00:00
-- url     : https://prove2.me/theorems/64fef1b6-c292-45ae-a17d-0335e2fa0f18
-- title:
--   Decomposition of the auxiliary function $K$ (Ge–Jin–Zheng Lemma 7; Chen–Li Lemma 4.7)
-- statement:
--   Let $U$ be any exact factor ($UU^\top=ZZ^\top$), $\Delta = X-U$, and let $\Omega$ be symmetric. Define $K(X)=\langle\Delta,\nabla^2f(X)[\Delta]\rangle-4\langle\nabla f(X),\Delta\rangle$. Then, **exactly**,
--
--   $$K(X)=\bigl\|P_\Omega(\Delta\Delta^\top)\bigr\|_F^2-3\bigl\|P_\Omega(XX^\top-UU^\top)\bigr\|_F^2+\lambda\Bigl(\langle\Delta,\nabla^2R(X)[\Delta]\rangle-4\langle\nabla R(X),\Delta\rangle\Bigr).$$
--
--   This algebraic identity is the heart of the unified landscape analysis: at a local minimum $K(X)\ge 0$ by the optimality conditions, yet the right-hand side is negative unless $\Delta=0$ — a single computation replacing the case analysis of Ge–Lee–Ma's original proof. The identity is pure algebra: no sampling model, no incoherence, no tuning conditions enter.
--
--   **Formalization Note** In Chen–Li's notation the right side is $K_1+K_2+K_3$ with $K_4=0$ since the residual $N$ vanishes in the exact rank-$r$ case; the population/deviation split $K_1+K_2 = \|P_\Omega(\cdot)\|^2$-form is recombined here.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], p. 18, Lemma 4.7, eq. (4.6), exact-rank case N = 0 (the K_1+K_2 population/deviation split recombined into ||P_Omega(.)||_F^2 form). Provenance: this is Ge, Jin, Zheng 2017, No Spurious Local Minima in Nonconvex Low Rank Problems, https://arxiv.org/abs/1704.00708, p. 7, Lemma 7, restated by Chen-Li with sampling notation.

import Definitions.Def_MCNoSpuriousMinModel
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.K_decomposition
    {d r : ℕ} (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (lam α : ℝ)
    (hsym : ∀ i j : Fin d, (i, j) ∈ Ω ↔ (j, i) ∈ Ω)
    (hU : U * Uᵀ = Z * Zᵀ) :
    Kfun Z Ω lam α X U =
      frobSq (projSet Ω ((X - U) * (X - U)ᵀ))
        - 3 * frobSq (projSet Ω (X * Xᵀ - U * Uᵀ))
        + lam * (regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)) := by sorry

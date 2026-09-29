-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_optimality_conditions
-- name    : MatrixCompletion.NoSpuriousMin.optimality_conditions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:11:43.880797+00:00
-- url     : https://prove2.me/theorems/060397a1-d6c7-4738-9733-986d90e78eda
-- title:
--   First- and second-order optimality conditions of the objective (Chen–Li Lemma 4.3; GLM Prop. 5.1)
-- statement:
--   Let $f(X)=\tfrac12\|P_\Omega(ZZ^\top-XX^\top)\|_F^2+\lambda R(X)$ with $\lambda\ge0$, threshold $\alpha>0$, and a **symmetric** observation set $\Omega$ (as in Chen–Li's off-diagonal symmetric sampling model, where symmetry is ambient). If $X$ is a local minimum of $f$, then $X$ satisfies the explicit first-order condition
--
--   $$2\,P_\Omega(ZZ^\top)X=2\,P_\Omega(XX^\top)X+\lambda\nabla R(X)$$
--
--   and, for every direction $V\in\mathbb{R}^{d\times r}$, the second-order condition
--
--   $$\|P_\Omega(VX^\top+XV^\top)\|_F^2+\lambda\,\langle V,\nabla^2R(X)[V]\rangle\ \ge\ 2\,\langle P_\Omega(ZZ^\top-XX^\top),\,VV^\top\rangle.$$
--
--   Together these give $K(\hat X)\ge0$ at every local minimum — the entry point of the Chen–Li superlevel-set argument.
--
--   **Formalization Note** The symmetry of $\Omega$ is a genuine hypothesis of the first-order clause, not a convenience: the gradient of the sampled term is $(P_\Omega(S')+P_\Omega(S')^\top)X$ for $S'=XX^\top-ZZ^\top$, which equals $2P_\Omega(S')X$ exactly when $P_\Omega(S')$ is symmetric. For non-symmetric $\Omega$ there are strict local minima at which $2P_\Omega(S')X+\lambda\nabla R(X)\ne0$, so the clause would be false as stated. The second-order clause holds regardless; the hypothesis is stated once for the conjunction.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], pp. 16-17, Lemma 4.3 (first- and second-order optimality conditions; yields K(X) >= 0 at every local minimum). Provenance: restated there from Ge, Lee, Ma 2016, https://arxiv.org/abs/1605.07272 (v4), p. 11, Proposition 5.1. The symmetry of Omega, ambient in Chen-Li's off-diagonal symmetric Bernoulli model (their Definition 1), is carried as an explicit hypothesis; the first-order clause is false without it.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Instances.Matrix
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.optimality_conditions
    {d r : ℕ} (Z X : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (lam α : ℝ) (hlam : 0 ≤ lam) (hα : 0 < α)
    (hsym : ∀ i j : Fin d, (i, j) ∈ Ω ↔ (j, i) ∈ Ω)
    (hmin : IsLocalMin (objective Z Ω lam α) X) :
    FirstOrderPt Z Ω lam α X ∧ SecondOrderPt Z Ω lam α X := by sorry

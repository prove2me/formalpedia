-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_regularizer_gradient
-- name    : MatrixCompletion.NoSpuriousMin.regularizer_gradient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:11:33.584356+00:00
-- url     : https://prove2.me/theorems/b6d4b8fd-2e67-4ca1-b99c-6628f5063948
-- title:
--   Gradient of the incoherence regularizer $\nabla R(X)=\Gamma X$ (Prop. 5.2)
-- statement:
--   Let $R(X)=\sum_{i=1}^d(\|X_i\|-\alpha)_+^4$ be the row regularizer with threshold $\alpha>0$. For any matrices $X,V\in\mathbb{R}^{d\times r}$, the map $s\mapsto R(X+sV)$ is differentiable at $s=0$ with derivative
--
--   $$\frac{d}{ds}R(X+sV)\Big|_{s=0}=\langle\Gamma X,\,V\rangle,\qquad \Gamma_{ii}=\frac{4(\|X_i\|-\alpha)_+^3}{\|X_i\|},$$
--
--   i.e. the regularizer has gradient $\nabla R(X)=\Gamma X$ with $\Gamma$ diagonal and $\Gamma_{ii}\ge 0$. This is the calculus identity behind the explicit first- and second-order conditions used throughout the mission.
--
--   **Formalization Note** The paper prints the exponent $4$ in $\Gamma_{ii}$; the derivative of $(t-\alpha)_+^4$ is $4(t-\alpha)_+^3$, the form its rank-1 counterpart on p. 9 uses, so the cube is the intended reading. The statement is expressed as a directional derivative, which avoids fixing a norm on matrix space.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], pp. 16-19: the gradient formula inside Lemma 4.3 and the explicit expansion of vec(D)^T Grad^2 G_alpha(X) vec(D) - 4<Grad G_alpha(X), D> displayed after Lemma 4.7. Provenance: Ge, Lee, Ma 2016, Matrix Completion has No Spurious Local Minimum, https://arxiv.org/abs/1605.07272 (v4), p. 11, Proposition 5.2 (whose printed exponent 4 is corrected to 3, per the derivative of (t-alpha)_+^4 and the rank-1 form on its p. 9); explicit Hessian form also Ge, Jin, Zheng 2017, No Spurious Local Minima in Nonconvex Low Rank Problems, https://arxiv.org/abs/1704.00708, Lemma 18.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Analysis.Calculus.Deriv.Basic
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.regularizer_gradient
    {d r : ℕ} (α : ℝ) (hα : 0 < α) (X V : Matrix (Fin d) (Fin r) ℝ) :
    HasDerivAt (fun s : ℝ => reg α (X + s • V)) (innerM (regGrad α X) V) 0 := by sorry

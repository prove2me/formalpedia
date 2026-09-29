-- Prove2me | Theorems.Thm_DinhSharpness_DerivativeTransformation
-- name    : DinhSharpness.DerivativeTransformation
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T03:04:26.660263+00:00
-- url     : https://prove2.me/theorems/7de16b7a-a9f3-4a95-a85b-8cbca4506204
-- title:
--   Theorem 3 — Transformation of the Gradient and Hessian
-- statement:
--   Let $L$ be continuous and satisfy the local twice
--   Fréchet differentiability condition at $\theta$. For every $\alpha>0$, the
--   same regularity holds at $T_\alpha\theta$, and for all parameter directions $u,w$,
--   $$DL(T_\alpha\theta)[u]=DL(\theta)[T_{\alpha^{-1}}u],$$
--   $$H_L(T_\alpha\theta)[u,w]
--     =H_L(\theta)[T_{\alpha^{-1}}u,T_{\alpha^{-1}}w].$$
--   No critical-point or minimum assumption is imposed here. Formalization note:
--   direct source Theorem 3, expressing its row-gradient formula as equality of
--   linear functionals and its Hessian congruence as equality on two arguments.
--   Transport of local regularity records that these are actual derivatives.
--
--   Source: Laurent Dinh, Razvan Pascanu, Samy Bengio, Yoshua Bengio, Sharp Minima Can Generalize For Deep Nets, ICML 2017, arXiv:1703.04933v2, https://arxiv.org/abs/1703.04933v2; Section 4.2, PDF p. 5, Theorem 3 and its unnumbered first- and second-derivative identities; Section 2, PDF p. 2.
--
--   ### Notation and network conventions
--   Let $d,h\ge1$ be the input dimension and hidden width. The parameter
--   $\theta=(W,v)$ consists of $W\in\mathbb R^{d\times h}$ and $v\in\mathbb R^h$,
--   with the Euclidean norm on all $n=dh+h$ entries. The scalar-output network is
--   $$f_\theta(x)=\sum_{j=1}^h \max\!\left(\sum_{i=1}^d x_i W_{ij},0\right)v_j,
--   \qquad x\in\mathbb R^d.$$
--   There are no biases and no output activation. For any real-valued functional
--   $\ell$ on prediction functions, $L(\theta)=\ell(f_\theta)$. In particular,
--   losses with additional parameter-dependent penalties are not included unless
--   they also admit this representation. The positive rescaling is
--   $$T_\alpha(W,v)=(\alpha W,\alpha^{-1}v),\qquad \alpha>0.$$
--   Observational equivalence means equality of predictions on every input.
--
--   The local regularity condition means that $L$ is Fréchet differentiable at
--   every point of some neighborhood of $\theta$, and the map $z\mapsto DL(z)$ is
--   Fréchet differentiable at $\theta$. Write
--   $H_L(\theta)=D(DL)(\theta)$, a continuous bilinear form. Its norm is
--   $$\|H_L(\theta)\|=\sup_{\|u\|\le1,\,\|w\|\le1}
--          |H_L(\theta)[u,w]|.$$
--   Under Euclidean/Riesz identification, this is the spectral operator norm of
--   the Hessian matrix. A local minimum uses the usual Euclidean neighborhood;
--   it need not be isolated or global. No probability model is assumed: the claim
--   is deterministic and compares the same prediction function.
--
--   Formalization note: the network and scaling directly encode Section 3,
--   Definition 3 (PDF p. 3), Theorem 1 and Definition 5 (PDF p. 4).
--   The function-based continuous-loss convention is Section 2, PDF p. 2.
--   For the Hessian targets, the local regularity condition makes the source's
--   implicit second differentiability explicit without requiring global smoothness
--   or continuity of second derivatives. The model defines actual Fréchet
--   derivatives, not an arbitrary matrix constrained by desired conclusions.
--   Relevant displayed formulas have no equation numbers.
-- source:
--   Laurent Dinh, Razvan Pascanu, Samy Bengio, Yoshua Bengio, Sharp Minima Can Generalize For Deep Nets, ICML 2017, arXiv:1703.04933v2, https://arxiv.org/abs/1703.04933v2; Section 4.2, PDF p. 5, Theorem 3 and its unnumbered first- and second-derivative identities; Section 2, PDF p. 2.

import Definitions.Def_DinhSharpness_Model

namespace DinhSharpness
theorem DerivativeTransformation :
  ∀ (d h : ℕ), 0 < d → 0 < h →
    ∀ (ℓ : (Input d → ℝ) → ℝ), Continuous (parameterLoss (h := h) ℓ) →
      ∀ (θ : Parameter d h), TwiceDifferentiableAt (parameterLoss ℓ) θ →
        ∀ (α : ℝ), 0 < α →
          TwiceDifferentiableAt (parameterLoss ℓ) (scale α θ) ∧
          (∀ u : Parameter d h,
            fderiv ℝ (parameterLoss ℓ) (scale α θ) u =
              fderiv ℝ (parameterLoss ℓ) θ (scale α⁻¹ u)) ∧
          (∀ u v : Parameter d h,
            hessian (parameterLoss ℓ) (scale α θ) u v =
              hessian (parameterLoss ℓ) θ (scale α⁻¹ u) (scale α⁻¹ v)) := by sorry
end DinhSharpness

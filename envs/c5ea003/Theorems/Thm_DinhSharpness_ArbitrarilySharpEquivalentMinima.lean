-- Prove2me | Theorems.Thm_DinhSharpness_ArbitrarilySharpEquivalentMinima
-- name    : DinhSharpness.ArbitrarilySharpEquivalentMinima
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T03:04:41.002374+00:00
-- url     : https://prove2.me/theorems/e6464e81-4082-4fc9-9933-327ee80f29be
-- title:
--   Theorem 4 — Arbitrarily Sharp Observationally Equivalent Minima
-- statement:
--   Let the parameter loss $L$ be continuous. Suppose
--   $\theta$ is a local minimum, $DL(\theta)=0$, the local twice Fréchet
--   differentiability condition holds, and $H_L(\theta)\ne0$. Then
--   $$\forall M>0\ \exists\alpha>0:\quad
--           M\le\|H_L(T_\alpha\theta)\|.$$
--   For that same $\alpha$, predictions on every input and the loss value are
--   unchanged; $T_\alpha\theta$ is again a critical local minimum satisfying the
--   same local regularity. No condition $W\ne0$ or $v\ne0$ is added.
--
--   Formalization note: direct source Theorem 4, including its accompanying
--   observational-equivalence interpretation and explicitly stating the regularity
--   implicit in the Hessian notation. This is the full arbitrary-dimensional,
--   one-hidden-layer result, not a prescribed scalar example or an assumed
--   Hessian-transformation rule. It asserts a parameterization dependence of
--   sharpness; it is not a statistical generalization bound.
--
--   Source: Laurent Dinh, Razvan Pascanu, Samy Bengio, Yoshua Bengio, Sharp Minima Can Generalize For Deep Nets, ICML 2017, arXiv:1703.04933v2, https://arxiv.org/abs/1703.04933v2; Section 4.2, PDF p. 5, Theorem 4 (Sharpest direction); proof and interpretation continue on PDF p. 6; Section 2, PDF p. 2. Displays are unnumbered.
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
--   Laurent Dinh, Razvan Pascanu, Samy Bengio, Yoshua Bengio, Sharp Minima Can Generalize For Deep Nets, ICML 2017, arXiv:1703.04933v2, https://arxiv.org/abs/1703.04933v2; Section 4.2, PDF p. 5, Theorem 4 (Sharpest direction); proof and interpretation continue on PDF p. 6; Section 2, PDF p. 2. Displays are unnumbered.

import Definitions.Def_DinhSharpness_Model

namespace DinhSharpness
theorem ArbitrarilySharpEquivalentMinima :
  ∀ (d h : ℕ), 0 < d → 0 < h →
    ∀ (ℓ : (Input d → ℝ) → ℝ), Continuous (parameterLoss (h := h) ℓ) →
      ∀ (θ : Parameter d h), TwiceDifferentiableAt (parameterLoss ℓ) θ →
        IsLocalMin (parameterLoss ℓ) θ → fderiv ℝ (parameterLoss ℓ) θ = 0 →
          hessian (parameterLoss ℓ) θ ≠ 0 →
            ∀ M : ℝ, 0 < M → ∃ α : ℝ, 0 < α ∧
              prediction (scale α θ) = prediction θ ∧
              parameterLoss ℓ (scale α θ) = parameterLoss ℓ θ ∧
              IsLocalMin (parameterLoss ℓ) (scale α θ) ∧
              TwiceDifferentiableAt (parameterLoss ℓ) (scale α θ) ∧
              fderiv ℝ (parameterLoss ℓ) (scale α θ) = 0 ∧
              M ≤ ‖hessian (parameterLoss ℓ) (scale α θ)‖ := by sorry
end DinhSharpness

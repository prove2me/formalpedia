-- Prove2me | Definitions.Def_DinhSharpness_Model
-- name    : DinhSharpness_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-26T03:03:42.908145+00:00
-- url     : https://prove2.me/theorems/21896a54-3107-4b33-bff1-30954cddc98e
-- title:
--   ReLU Networks, Reciprocal Layer Scaling, and the Euclidean Hessian
-- statement:
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
--
--
--   Source: Laurent Dinh, Razvan Pascanu, Samy Bengio, Yoshua Bengio, Sharp Minima Can Generalize For Deep Nets, ICML 2017, arXiv:1703.04933v2, https://arxiv.org/abs/1703.04933v2; Section 2, PDF p. 2; Section 3, PDF p. 4, Theorem 1 and Definition 5; Section 4.2, PDF p. 5, Theorems 3–4. Displays are unnumbered.
-- source:
--   Laurent Dinh, Razvan Pascanu, Samy Bengio, Yoshua Bengio, Sharp Minima Can Generalize For Deep Nets, ICML 2017, arXiv:1703.04933v2, https://arxiv.org/abs/1703.04933v2; Section 2, PDF p. 2; Section 3, PDF p. 3 and PDF p. 4, Definitions 3–5 and Theorem 1; Section 4.2, PDF p. 5, Theorems 3–4. Displays are unnumbered.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
Parameter geometry for Dinh--Pascanu--Bengio--Bengio, arXiv:1703.04933v2.
Source: Section 2, PDF p. 2; Section 3, PDF pp. 3--4, Definitions 3--5;
Section 4.2, PDF p. 5, Theorems 3--4 (unnumbered displays).
-/

noncomputable section

open scoped Topology

namespace DinhSharpness

/-- Input vectors with their Euclidean norm. -/
abbrev Input (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- First-layer matrix entries followed by the scalar output layer's weights. -/
abbrev Coordinate (d h : ℕ) := (Fin d × Fin h) ⊕ Fin h

/-- The Euclidean norm here is essential to the spectral-norm interpretation. -/
abbrev Parameter (d h : ℕ) := EuclideanSpace ℝ (Coordinate d h)

/-- The paper's rectified activation. -/
def relu (t : ℝ) : ℝ := max t 0

/-- One hidden layer, no biases, and a scalar linear output. -/
def prediction {d h : ℕ} (θ : Parameter d h) (x : Input d) : ℝ :=
  ∑ j : Fin h, relu (∑ i : Fin d, x i * θ (Sum.inl (i, j))) * θ (Sum.inr j)

/-- The parameter loss is computed from the complete prediction function. -/
def parameterLoss {d h : ℕ} (ℓ : (Input d → ℝ) → ℝ) (θ : Parameter d h) : ℝ :=
  ℓ (prediction θ)

/-- Positive reciprocal layer rescaling; theorems explicitly require `0 < α`. -/
def scale {d h : ℕ} (α : ℝ) (θ : Parameter d h) : Parameter d h :=
  WithLp.toLp 2 (fun k ↦ match k with
    | Sum.inl ij => α * θ (Sum.inl ij)
    | Sum.inr j => α⁻¹ * θ (Sum.inr j))

/-- Explicit local regularity: an actual derivative nearby and its derivative at the point. -/
def TwiceDifferentiableAt {d h : ℕ} (L : Parameter d h → ℝ)
    (θ : Parameter d h) : Prop :=
  (∀ᶠ z in 𝓝 θ, DifferentiableAt ℝ L z) ∧ DifferentiableAt ℝ (fderiv ℝ L) θ

/-- The actual second Fréchet derivative, as a continuous bilinear form. -/
def hessian {d h : ℕ} (L : Parameter d h → ℝ) (θ : Parameter d h) :
    Parameter d h →L[ℝ] Parameter d h →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ L) θ

end DinhSharpness



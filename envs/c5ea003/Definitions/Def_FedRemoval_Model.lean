-- Prove2me | Definitions.Def_FedRemoval_Model
-- name    : FedRemoval_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-28T21:40:45.095884+00:00
-- url     : https://prove2.me/theorems/8f53f14c-0e36-4239-a1cd-22c0d9fc3f6d
-- title:
--   Affine-Feature Ridge Regression and Finite Removal Laws
-- statement:
--   The definition bundle supplies fixed affine predictors,
--   normalized ridge objectives on retained index sets, their computed Gram
--   operators, Hessians, linear terms and inverse-defined optima, the exact Newton
--   correction, the server quadratic removal surrogate, its gap and mismatch
--   factor, and finite probability laws with weighted means and mean-square error.
--   Client ownership also defines a retained index set by excluding one client.
--   No theorem is asserted in this bundle.
--
--   ### Notation and hypotheses
--   The full dataset has $n$ records and the server dataset has $q$ records.
--   Record $i$ has a fixed real linear feature map $A_i:\mathbb R^d\to\mathbb R^k$,
--   offset $a_i\in\mathbb R^k$, and target $y_i\in\mathbb R^k$.
--   For a retained subset $S$ and regularization $\mu$, define
--   $$L_S(w)=\frac1{2|S|}\sum_{i\in S}\|A_iw+a_i-y_i\|^2+
--   \frac\mu2\|w\|^2,\quad
--   G_S=\frac1{|S|}\sum_{i\in S}A_i^*A_i,\quad H_S=G_S+\mu I,$$
--   $$b_S=\frac1{|S|}\sum_{i\in S}A_i^*(y_i-a_i),\quad
--   u_S=H_S^{-1}b_S,\quad g_S(w)=H_Sw-b_S.$$
--   Here $u_D$ uses all full-data indices, and $H_P,G_P$ use all server indices.
--   Only the server feature maps enter its removal surrogate; server targets and offsets are unused.
--   All norms are Euclidean vector or induced operator norms, as appropriate.
--   The inverse is the total ring inverse; theorems must derive its validity from
--   $\mu>0$, not assume it. Empty empirical averages are defined by Lean's total
--   arithmetic, but the relevant theorems require $S\ne\varnothing$ and, when
--   server data appear, $q>0$. Zero parameter or output dimension is allowed.
--
--   Set
--   $$F_w(v)=\tfrac12\langle v,H_Pv\rangle-\langle g_S(w),v\rangle,
--   \quad v_P(w)=H_P^{-1}g_S(w),\quad
--   \operatorname{gap}(w,v)=F_w(v)-F_w(v_P(w)),
--   \quad\kappa=\|H_P^{-1}\|\|G_P-G_S\|.$$
--
--   The probability model used only by the final target is a finite joint law
--   on $\Omega=\{0,\ldots,N-1\}$: masses $p_\omega\ge0$ sum to one and
--   $\mathbb E[f]=\sum_{\omega\in\Omega}p_\omega f(\omega)$.
--   It allows arbitrary dependence between outputs. No law exists for $N=0$.
--   The other targets are deterministic and assume no probability model.
--
--   Formalization note: the fixed affine-feature model is source-derived from
--   Jin et al., arXiv:2306.02216v3, Section III-A (Section 3), PDF p. 3,
--   equation (3), and PDF p. 4, equations (4)--(5). Arbitrary real targets and
--   nonempty retained subsets explicitly extend the one-hot/client-removal
--   setting. The finite-law error targets are corrected formulations, not
--   transcriptions or proofs of the printed Theorem 2.
-- source:
--   Ruinan Jin, Minghui Chen, Qiong Zhang, Xiaoxiao Li, Forgettable Federated Linear Learning with Certified Data Unlearning, IEEE TNNLS (2026), arXiv:2306.02216v3, https://arxiv.org/pdf/2306.02216v3; Section II-B (Section 2), PDF p. 3, equation (1). Section III-A (Section 3), PDF p. 3 and PDF p. 4, equations (3)--(5); supplementary Section C2, PDF p. 13, Condition 5. Section III-B (Section 3), PDF p. 5, equation (6). Section III-C (Section 3), PDF p. 5 and PDF p. 6, Theorem 2; supplementary Section C5, PDF p. 16, unnumbered error-decomposition and inverse-perturbation displays.

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Affine-feature ridge regression and finite probability laws for the corrected FedRemoval draft.
Source: Jin et al., arXiv:2306.02216v3, Section II-B, PDF p. 3, equation (1);
Sections III-A--III-C, PDF pp. 3--6, equations (3)--(6), Theorem 2;
supplementary Section C5, PDF p. 16. The error targets are explicitly corrected
source-derived statements, not transcriptions of the printed Theorem 2.
-/

noncomputable section

open scoped BigOperators

namespace FedRemoval

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Fixed affine features; the offset includes the frozen linearization point. -/
structure Data (n d k : ℕ) where
  feature : Fin n → E d →L[ℝ] E k
  offset : Fin n → E k
  target : Fin n → E k

def predict {n d k : ℕ} (D : Data n d k) (i : Fin n) (w : E d) : E k :=
  D.feature i w + D.offset i

def loss {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n)) (μ : ℝ) (w : E d) : ℝ :=
  (2 * (s.card : ℝ))⁻¹ * (∑ i ∈ s, ‖predict D i w - D.target i‖ ^ 2) +
    μ / 2 * ‖w‖ ^ 2

def gram {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n)) : E d →L[ℝ] E d :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, (D.feature i).adjoint.comp (D.feature i)

def rhs {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n)) : E d :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, (D.feature i).adjoint (D.target i - D.offset i)

def hessian {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n)) (μ : ℝ) :
    E d →L[ℝ] E d :=
  gram D s + μ • ContinuousLinearMap.id ℝ (E d)

def ridgeGradient {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) (w : E d) : E d :=
  hessian D s μ w - rhs D s

def inverseHessian {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) : E d →L[ℝ] E d :=
  Ring.inverse (hessian D s μ)

def optimum {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n)) (μ : ℝ) : E d :=
  inverseHessian D s μ (rhs D s)

/-- A client's removal is one special case of choosing the retained index set. -/
def retainedIndices {n C : ℕ} (owner : Fin n → Fin C) (c : Fin C) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ owner i ≠ c)

def exactCorrection {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) (w : E d) : E d :=
  inverseHessian D s μ (ridgeGradient D s μ w)

def surrogate {n q d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (P : Data q d k) (μ : ℝ) (w v : E d) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ v (hessian P Finset.univ μ v) -
    inner ℝ (ridgeGradient D s μ w) v

def surrogateOptimum {n q d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (P : Data q d k) (μ : ℝ) (w : E d) : E d :=
  inverseHessian P Finset.univ μ (ridgeGradient D s μ w)

def mismatch {n q d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (P : Data q d k) (μ : ℝ) : ℝ :=
  ‖inverseHessian P Finset.univ μ‖ * ‖gram P Finset.univ - gram D s‖

def solverGap {n q d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (P : Data q d k) (μ : ℝ) (w v : E d) : ℝ :=
  surrogate D s P μ w v - surrogate D s P μ w (surrogateOptimum D s P μ w)

/-- A finite joint law; its output maps may be dependent. -/
structure Law (N : ℕ) where
  mass : Fin N → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

def mean {N : ℕ} (p : Law N) (f : Fin N → ℝ) : ℝ :=
  ∑ i, p.mass i * f i

def mse {N d : ℕ} (p : Law N) (w : Fin N → E d) (u : E d) : ℝ :=
  mean p (fun i ↦ ‖w i - u‖ ^ 2)

end FedRemoval



-- Prove2me | Definitions.Def_FeatureDistortion_Model
-- name    : FeatureDistortion_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-26T21:15:22.584548+00:00
-- url     : https://prove2.me/theorems/1aa31c06-778b-4b10-b155-1c7b43e700bb
-- title:
--   Two-layer linear regression and gradient-flow model
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   **Vec.** For each natural number $d$, $\operatorname{Vec}(d)$ is the real Euclidean space with coordinates indexed by $\{0,\ldots,d-1\}$, with its usual inner product and norm. The case $d=0$ is included and consists only of the zero vector.
--
--   **Features.** For natural numbers $d,k$, $\operatorname{Features}(d,k)$ is the space of continuous real-linear maps $\mathbb R^d\to\mathbb R^k$. There is no rank or normalization assumption. If either dimension is zero, this space consists only of the zero map.
--
--   **weights.** For natural numbers $d,k$, a continuous real-linear map $B:\mathbb R^d\to\mathbb R^k$, and $v\in\mathbb R^k$, the weight vector is $B^*v\in\mathbb R^d$, where $B^*$ is the Euclidean adjoint. Zero dimensions are permitted; the weight vector is zero if $d=0$ or $k=0$.
--
--   **residual.** For natural numbers $n,d,k$, continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B:\mathbb R^d\to\mathbb R^k$, and vectors $Y\in\mathbb R^n$ and $v\in\mathbb R^k$, the residual is $XB^*v-Y$. All dimensions may be zero; the residual is zero if $n=0$ and is $-Y$ if $d=0$ or $k=0$. There is no required relation between the arguments.
--
--   **trainingLoss.** For natural numbers $n,d,k$, continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B:\mathbb R^d\to\mathbb R^k$, and vectors $Y\in\mathbb R^n$ and $v\in\mathbb R^k$, the training loss is $\|XB^*v-Y\|^2$. There is no normalization by $n$ or factor of $1/2$. If $n=0$ it is zero; if $d=0$ or $k=0$ it is $\|Y\|^2$.
--
--   **headGradient.** For natural numbers $n,d,k$, continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B:\mathbb R^d\to\mathbb R^k$, and vectors $Y\in\mathbb R^n$ and $v\in\mathbb R^k$, this definition assigns the vector $2BX^*(XB^*v-Y)\in\mathbb R^k$, where the adjoints are Euclidean. There are no further hypotheses. The vector is zero if any of the dimensions is zero.
--
--   **featureGradient.** For natural numbers $n,d,k$, continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B:\mathbb R^d\to\mathbb R^k$, and vectors $Y\in\mathbb R^n$ and $v\in\mathbb R^k$, this definition assigns the continuous real-linear map $x\mapsto2\langle X^*(XB^*v-Y),x\rangle v$ from $\mathbb R^d$ to $\mathbb R^k$. Thus the rank-one map takes an inner product with $X^*(XB^*v-Y)$ and multiplies $v$ by that scalar. No dimension is required to be positive; the map is zero if any of $n,d,k$ is zero.
--
--   **Trajectory.** For natural numbers $d,k$, a trajectory is a pair of functions $a:\mathbb R\to\mathbb R^k$ and $F:\mathbb R\to\mathcal L(\mathbb R^d,\mathbb R^k)$, called its head and features, respectively; $\mathcal L$ denotes continuous real-linear maps. The structure itself imposes no continuity, differentiability, initial condition, or differential equation on these functions. Both are defined at all real times, and zero dimensions are permitted.
--
--   **IsFineTuningFlow.** For natural numbers $n,d,k$, continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_0:\mathbb R^d\to\mathbb R^k$, vectors $Y\in\mathbb R^n$ and $v_0\in\mathbb R^k$, and a pair of functions $a:\mathbb R\to\mathbb R^k$ and $F:\mathbb R\to\mathcal L(\mathbb R^d,\mathbb R^k)$, this predicate means $a(0)=v_0$, $F(0)=B_0$, and, for every real $t\geq0$, existence of derivatives within $[0,\infty)$ equal to $\dot a(t)=-2F(t)X^*(XF(t)^*a(t)-Y)$ and $\dot F(t)=\bigl[x\mapsto-2\langle X^*(XF(t)^*a(t)-Y),x\rangle a(t)\bigr]$. The latter is a derivative in the space of continuous linear maps. At zero, the derivatives are within the half-line. No conditions apply at negative times. Zero dimensions are allowed.
--
--   **IsLinearProbingFlow.** For natural numbers $n,d,k$, continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_0:\mathbb R^d\to\mathbb R^k$, vectors $Y\in\mathbb R^n$ and $v_0\in\mathbb R^k$, and a function $a:\mathbb R\to\mathbb R^k$, this predicate means $a(0)=v_0$ and existence, at every real $t\geq0$, of a derivative within $[0,\infty)$ equal to $-2B_0X^*(XB_0^*a(t)-Y)$. The map $B_0$ is fixed. Values at negative times are unconstrained, and zero dimensions are included.
--
--   **rowSpace.** For natural numbers $d,n$ and a continuous real-linear map $X:\mathbb R^d\to\mathbb R^n$, this definition assigns the subspace $\{X^*z:z\in\mathbb R^n\}$ of $\mathbb R^d$, where $X^*$ is the Euclidean adjoint. It is the zero subspace if $X=0$, $n=0$, or $d=0$.
--
--   **OrthonormalRows.** For natural numbers $d,k$ and a continuous real-linear map $B:\mathbb R^d\to\mathbb R^k$, this predicate means $BB^*=I_{\mathbb R^k}$, equivalently $BB^*v=v$ for every $v\in\mathbb R^k$. It holds for the unique map when $k=0$; it cannot hold when $d=0<k$.
--
--   **VisibleOn.** For natural numbers $d,k$, a continuous real-linear map $B:\mathbb R^d\to\mathbb R^k$, and a real linear subspace $S\subseteq\mathbb R^d$, this predicate means that $v\mapsto\Pi_S(B^*v)$ is injective, where $\Pi_S$ is orthogonal projection: equality of these projections for any $v_1,v_2\in\mathbb R^k$ implies $v_1=v_2$. If $k=0$ this holds; if $S=\{0\}$ and $k>0$ it cannot hold. Zero dimensions are included.
--
--   **balance.** For natural numbers $d,k$, a vector $v\in\mathbb R^k$, and a continuous real-linear map $B:\mathbb R^d\to\mathbb R^k$, the balance is the endomorphism of $\mathbb R^k$ sending $z$ to $\langle v,z\rangle v-BB^*z$, namely $vv^{\mathsf T}-BB^*$. No normalization is required. It is the zero endomorphism if $k=0$, and its second summand is zero if $d=0$.
--
--   **alignmentError.** For a natural number $k$ and vectors $v_0,u\in\mathbb R^k$, the alignment error is $\left|\langle v_0,u\rangle^2-\langle u,u\rangle^2\right|=\left|\langle v_0,u\rangle^2-\|u\|^4\right|$. It vanishes exactly when $\langle v_0,u\rangle=\|u\|^2$ or $\langle v_0,u\rangle=-\|u\|^2$. No nonzero assumption is imposed. If $u=0$, including when $k=0$, the error is zero for every $v_0$.
--
--   **secondMoment.** For a natural number $d$ and any measure $\mu$ on $\mathbb R^d$, this definition assigns the operator-valued Bochner integral $\Sigma_\mu=\int(x\otimes x)\,d\mu(x)$, where $(x\otimes x)(w)=\langle x,w\rangle x$. It is an uncentered second moment. There is no probability or integrability assumption in this definition; the total Bochner integral is zero if its integrand is not integrable. For $d=0$ the operator is zero.
--
--   **OODLaw.** For a natural number $d$, an OOD law consists of a probability measure $\mu$ on $\mathbb R^d$, the hypothesis that $x\mapsto\|x\|^2$ is integrable with respect to $\mu$, and the hypothesis that $\langle w,\Sigma_\mu w\rangle>0$ for every nonzero $w\in\mathbb R^d$, where $\Sigma_\mu=\int(x\otimes x)\,d\mu(x)$ and $(x\otimes x)(z)=\langle x,z\rangle x$. There is no mean-zero assumption. For $d=0$, the positivity condition is vacuous and the probability measure is concentrated at the sole zero vector.
--
--   **oodLoss.** For natural numbers $d,k$, a probability measure $\mu$ on $\mathbb R^d$ with integrable squared norm and $\langle z,\Sigma_\mu z\rangle>0$ for every nonzero $z$, a target $w\in\mathbb R^d$, a vector $v\in\mathbb R^k$, and a continuous real-linear map $B:\mathbb R^d\to\mathbb R^k$, this definition assigns $\int\langle B^*v-w,x\rangle^2\,d\mu(x)$. Here $\Sigma_\mu=\int(x\otimes x)\,d\mu(x)$, with $(x\otimes x)(z)=\langle x,z\rangle x$, and $^*$ is the Euclidean adjoint. If $d=0$ the loss is zero; if $k=0$ it is $\int\langle-w,x\rangle^2\,d\mu(x)$.
--
--   **gaussianHead.** For a natural number $k$ and any real number $\sigma$, this definition assigns the pushforward of standard Gaussian measure on Euclidean $\mathbb R^k$ under $z\mapsto\sigma z$. Positive, negative, and zero $\sigma$ are all allowed. For $\sigma=0$ this is the point mass at zero; for $k=0$ it is the point mass at the only vector for every $\sigma$.
--
--   **Problem.** For natural numbers $n,d,k$, a problem consists of continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, called its data and optimal features; a real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, called its rotation; and a vector $u_\star\in\mathbb R^k$, called its optimal head. No other conditions are imposed on these fields. In particular, positive determinant is not required of $R$. Zero dimensions are included.
--
--   **initialFeatures.** For natural numbers $n,d,k$ and a problem with continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, a real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, the initial feature map is $RB_\star:\mathbb R^d\to\mathbb R^k$. It does not depend on $X$ or $u_\star$ and requires no admissibility hypothesis. If $d=0$ or $k=0$, it is zero.
--
--   **alignedHead.** For natural numbers $n,d,k$ and a problem with continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, a real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, the aligned head is $Ru_\star$. It does not depend on $X$ or $B_\star$ and requires no admissibility hypothesis. It is zero if $u_\star=0$, including when $k=0$.
--
--   **targetWeights.** For natural numbers $n,d,k$ and a problem with continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, a real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, the target vector is $B_\star^*u_\star\in\mathbb R^d$. It does not depend on $X$ or $R$ and requires no admissibility hypothesis. It is zero if $d=0$ or $k=0$.
--
--   **labels.** For natural numbers $n,d,k$ and a problem with continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, a real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, the label vector is $XB_\star^*u_\star\in\mathbb R^n$. It does not depend on $R$ and requires no admissibility hypothesis. It is zero if any of $n,d,k$ is zero.
--
--   **Admissible.** For natural numbers $n,d,k$ and a problem consisting of continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, a real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, let $B_0=RB_\star$, $S=\{X^*z:z\in\mathbb R^n\}$, and $r=\dim_{\mathbb R}S$. Admissibility is the conjunction $0<k$, $k\leq r$, $r+k<d$, $B_\star B_\star^*=I_{\mathbb R^k}$, $u_\star\neq0$, injectivity of $v\mapsto\Pi_S(B_0^*v)$, and injectivity of $v\mapsto\Pi_{S^\perp}(B_0^*v)$, both on $\mathbb R^k$, where $\Pi$ denotes orthogonal projection. Each injectivity requirement says equality of the displayed projections of two vectors implies equality of the vectors. These hypotheses exclude zero dimensions and require $n\geq k$ and $d\geq2k+1$.
--
--   Formalization note: source-derived model for the source-backed parent; no flow existence, convergence, invariant, or desired risk bound is assumed. Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Section 3.1, PDF pp. 4--6, equations (3.2)--(3.5). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Section 3.1, PDF pp. 4--6, equations (3.2)--(3.5). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
Two-layer linear regression and its gradient flows. Source: Kumar et al.,
arXiv:2202.10054v1, Sections 3.1 and 3.4, PDF pp. 4--6 and 10;
Appendix A.2, PDF pp. 23--26, and A.7, PDF pp. 45--47.
The feature flow is the explicit Frobenius-gradient equation (A.17).
The continuous-linear-map norm is the Euclidean operator norm.
-/

noncomputable section
open MeasureTheory

namespace FeatureDistortion

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Features (d k : ℕ) := Vec d →L[ℝ] Vec k

def weights {d k : ℕ} (B : Features d k) (v : Vec k) : Vec d := B.adjoint v

def residual {n d k : ℕ} (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v : Vec k) (B : Features d k) : Vec n := X (weights B v) - Y

def trainingLoss {n d k : ℕ} (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v : Vec k) (B : Features d k) : ℝ := ‖residual X Y v B‖ ^ 2

def headGradient {n d k : ℕ} (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v : Vec k) (B : Features d k) : Vec k :=
  (2 : ℝ) • B (X.adjoint (residual X Y v B))

def featureGradient {n d k : ℕ} (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v : Vec k) (B : Features d k) : Features d k :=
  (2 : ℝ) • InnerProductSpace.rankOne ℝ v (X.adjoint (residual X Y v B))

structure Trajectory (d k : ℕ) where
  head : ℝ → Vec k
  features : ℝ → Features d k

def IsFineTuningFlow {n d k : ℕ} (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v₀ : Vec k) (B₀ : Features d k) (γ : Trajectory d k) : Prop :=
  γ.head 0 = v₀ ∧ γ.features 0 = B₀ ∧
    ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt γ.head (-headGradient X Y (γ.head t) (γ.features t))
        (Set.Ici 0) t ∧
      HasDerivWithinAt γ.features (-featureGradient X Y (γ.head t) (γ.features t))
        (Set.Ici 0) t

def IsLinearProbingFlow {n d k : ℕ} (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v₀ : Vec k) (B₀ : Features d k) (v : ℝ → Vec k) : Prop :=
  v 0 = v₀ ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt v (-headGradient X Y (v t) B₀) (Set.Ici 0) t

def rowSpace {d n : ℕ} (X : Vec d →L[ℝ] Vec n) : Submodule ℝ (Vec d) :=
  LinearMap.range X.adjoint.toLinearMap

def OrthonormalRows {d k : ℕ} (B : Features d k) : Prop :=
  B.comp B.adjoint = ContinuousLinearMap.id ℝ (Vec k)

/-- In the stated dimension regime this is positivity of the smallest
principal-angle cosine, rather than merely a nonzero projection. -/
def VisibleOn {d k : ℕ} (B : Features d k) (S : Submodule ℝ (Vec d)) : Prop :=
  Function.Injective (fun v : Vec k => S.starProjection (B.adjoint v))

def balance {d k : ℕ} (v : Vec k) (B : Features d k) : Vec k →L[ℝ] Vec k :=
  InnerProductSpace.rankOne ℝ v v - B.comp B.adjoint

def alignmentError {k : ℕ} (v₀ u : Vec k) : ℝ :=
  |(inner ℝ v₀ u) ^ 2 - (inner ℝ u u) ^ 2|

/-- The uncentered second moment, not the centered covariance operator. -/
def secondMoment {d : ℕ} (μ : Measure (Vec d)) : Vec d →L[ℝ] Vec d :=
  ∫ x, InnerProductSpace.rankOne ℝ x x ∂μ

structure OODLaw (d : ℕ) where
  measure : Measure (Vec d)
  isProbability : IsProbabilityMeasure measure
  finiteSecondMoment : Integrable (fun x : Vec d => ‖x‖ ^ 2) measure
  positiveSecondMoment : ∀ w : Vec d, w ≠ 0 →
    0 < inner ℝ w (secondMoment measure w)

def oodLoss {d k : ℕ} (D : OODLaw d) (w : Vec d) (v : Vec k)
    (B : Features d k) : ℝ :=
  ∫ x, (inner ℝ (weights B v - w) x) ^ 2 ∂D.measure

def gaussianHead (k : ℕ) (σ : ℝ) : Measure (Vec k) :=
  (ProbabilityTheory.stdGaussian (Vec k)).map (fun z => σ • z)

structure Problem (n d k : ℕ) where
  data : Vec d →L[ℝ] Vec n
  optimalFeatures : Features d k
  rotation : Vec k ≃ₗᵢ[ℝ] Vec k
  optimalHead : Vec k

def initialFeatures {n d k : ℕ} (P : Problem n d k) : Features d k :=
  P.rotation.toLinearIsometry.toContinuousLinearMap.comp P.optimalFeatures

def alignedHead {n d k : ℕ} (P : Problem n d k) : Vec k :=
  P.rotation P.optimalHead

def targetWeights {n d k : ℕ} (P : Problem n d k) : Vec d :=
  weights P.optimalFeatures P.optimalHead

def labels {n d k : ℕ} (P : Problem n d k) : Vec n :=
  P.data (targetWeights P)

def Admissible {n d k : ℕ} (P : Problem n d k) : Prop :=
  0 < k ∧
  k ≤ Module.finrank ℝ (rowSpace P.data) ∧
  Module.finrank ℝ (rowSpace P.data) + k < d ∧
  OrthonormalRows P.optimalFeatures ∧
  P.optimalHead ≠ 0 ∧
  VisibleOn (initialFeatures P) (rowSpace P.data) ∧
  VisibleOn (initialFeatures P) (rowSpace P.data)ᗮ

end FeatureDistortion



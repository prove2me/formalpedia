-- Prove2me | Definitions.Def_BCN_SG_Model
-- name    : BCN_SG_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-25T21:27:50.629894+00:00
-- url     : https://prove2.me/theorems/dbc4e127-1e35-44c7-bdcf-8e07effb45c2
-- title:
--   Stochastic gradient model, moment assumptions, and numerical quantities
-- statement:
--   This definition bundle specifies the objective, stochastic process, moment assumptions, and numerical quantities. Its definitions establish none of the five target estimates.
--
--   ### Notation and probability model
--   Let $d\in\mathbb N$ and $F:\mathbb R^d\to\mathbb R$ have an actual gradient
--   $\nabla F$ at every point, with
--   $\|\nabla F(x)-\nabla F(y)\|\le L\|x-y\|$ for all $x,y$, where $L>0$.
--   On a probability space $(\Omega,\mathcal A,\mathbb P)$, let
--   $(\mathcal F_k)_{k\ge0}$ be an increasing family of sub-$\sigma$-algebras of
--   $\mathcal A$. The initial vector $w_0$ is deterministic. The iterate $w_k$
--   is strongly $\mathcal F_k$-measurable, and the sampled direction $g_k$ is
--   strongly $\mathcal F_{k+1}$-measurable with $\mathbb E\|g_k\|^2<\infty$.
--   For deterministic real step sizes $\alpha_k>0$, the algorithm is
--   $$w_{k+1}=w_k-\alpha_k g_k\quad\text{almost surely}.$$
--   An open set $U\subseteq\mathbb R^d$ contains every iterate almost surely,
--   and a real number $F_{\inf}$ satisfies $F(x)\ge F_{\inf}$ for all $x\in U$.
--   Put $m_k=\mathbb E[g_k\mid\mathcal F_k]$. Fix real constants
--   $0<\mu\le\mu_G$, $M\ge0$, $M_V\ge0$, and $M_G=M_V+\mu_G^2$.
--   The source's first- and second-moment assumptions are, almost surely for every $k$,
--   $$\nabla F(w_k)^\top m_k\ge\mu\|\nabla F(w_k)\|^2,
--   \qquad\|m_k\|\le\mu_G\|\nabla F(w_k)\|,$$
--   $$\mathbb E[\|g_k\|^2\mid\mathcal F_k]-\|m_k\|^2
--   \le M+M_V\|\nabla F(w_k)\|^2.$$
--   Write $q_k=\|\nabla F(w_k)\|^2$,
--   $A_K=\sum_{k=0}^{K-1}\alpha_k$,
--   $W_K=\mathbb E[\sum_{k=0}^{K-1}\alpha_k q_k]$, and
--   $G_K=\mathbb E[\sum_{k=0}^{K-1}q_k]$; empty sums are zero.
--   Define $F_*:=\inf_{x\in\mathbb R^d}F(x)$ using the actual objective's range
--   (Lean's real-valued `sInf`), and
--   $\Delta_k=\mathbb E[F(w_k)-F_*]$ when stating the strongly convex targets.
--   Those targets require $d\ge1$, positive strong-convexity modulus, and
--   $F_{\inf}=F_*$. The other targets permit $d=0$ and use the trajectory-region
--   lower bound $F_{\inf}$, without assuming a global minimizer.
--
--   Formalization note: these are source assumptions with explicit filtration,
--   measurability, and finite-second-moment conventions for genuine Bochner and
--   conditional expectations. The deterministic initialization and square-integrable
--   directions imply finite iterate second moments; objective and gradient moments
--   must be justified from smoothness in the proofs. The model assumes no expected
--   descent inequality, no gradient-gap inequality, and no convergence conclusion.
--   Local index $0$ is paper index $1$ throughout. Full-history conditioning follows
--   Algorithm 4.1, PDF p. 22, footnote 4; the model assumptions are Assumptions 4.1
--   and 4.3, PDF p. 23 and PDF p. 24, equations (4.6)–(4.9), in Section 4 of
--   Bottou–Curtis–Nocedal, *Optimization Methods for Large-Scale Machine Learning*:
--   https://arxiv.org/abs/1606.04838v3.
-- source:
--   Léon Bottou, Frank E. Curtis, Jorge Nocedal, Optimization Methods for Large-Scale Machine Learning, arXiv:1606.04838v3, https://arxiv.org/abs/1606.04838v3; Section 4, PDF p. 22, Algorithm 4.1 and footnote 4; PDF p. 23 and PDF p. 24, Assumptions 4.1 and 4.3, equations (4.6)–(4.9); PDF pp. 24–34, Lemma 4.4 and Theorems 4.6, 4.7, 4.8, and 4.10.

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration

/-!
Bottou, Curtis, Nocedal, arXiv:1606.04838v3, Section 4, PDF pp. 21–34.
Algorithm 4.1 and its conditional-process convention: PDF p. 22, footnote 4.
Assumptions 4.1/4.3: PDF pp. 23–24, equations (4.6)–(4.9).
The local index 0 is the paper's index 1. Finite second moments are explicit.
The model contains no descent inequality or convergence conclusion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology InnerProductSpace

namespace BCN

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Objective (d : ℕ) where
  F : Space d → ℝ
  L : ℝ
  L_pos : 0 < L
  hasGradient : ∀ x, HasGradientAt F (gradient F x) x
  smooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖

structure MomentConstants where
  μ : ℝ
  μG : ℝ
  M : ℝ
  MV : ℝ
  μ_pos : 0 < μ
  μ_le_μG : μ ≤ μG
  M_nonneg : 0 ≤ M
  MV_nonneg : 0 ≤ MV

def MomentConstants.MG (C : MomentConstants) : ℝ := C.MV + C.μG ^ 2

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

structure Run (P : Objective d) (C : MomentConstants)
    (prob : Measure Ω) [IsProbabilityMeasure prob] (α : ℕ → ℝ) where
  history : Filtration ℕ mΩ
  w : ℕ → Ω → Space d
  g : ℕ → Ω → Space d
  w0 : Space d
  initial : ∀ ω, w 0 ω = w0
  w_adapted : ∀ k, StronglyMeasurable[history k] (w k)
  g_adapted : ∀ k, StronglyMeasurable[history (k + 1)] (g k)
  g_squareIntegrable : ∀ k, MemLp (g k) 2 prob
  step_pos : ∀ k, 0 < α k
  update : ∀ k, w (k + 1) =ᵐ[prob] fun ω ↦ w k ω - α k • g k ω
  region : Set (Space d)
  region_open : IsOpen region
  in_region : ∀ k, ∀ᵐ ω ∂prob, w k ω ∈ region
  lower : ℝ
  lower_bound : ∀ x ∈ region, lower ≤ P.F x
  angle : ∀ k, ∀ᵐ ω ∂prob,
    C.μ * ‖gradient P.F (w k ω)‖ ^ 2 ≤
      ⟪gradient P.F (w k ω), prob[g k | history k] ω⟫_ℝ
  mean_norm : ∀ k, ∀ᵐ ω ∂prob,
    ‖prob[g k | history k] ω‖ ≤ C.μG * ‖gradient P.F (w k ω)‖
  variance : ∀ k, ∀ᵐ ω ∂prob,
    prob[(fun ω ↦ ‖g k ω‖ ^ 2) | history k] ω - ‖prob[g k | history k] ω‖ ^ 2 ≤
      C.M + C.MV * ‖gradient P.F (w k ω)‖ ^ 2

variable {P : Objective d} {C : MomentConstants} {prob : Measure Ω}
  [IsProbabilityMeasure prob] {α : ℕ → ℝ}

def loss (R : Run P C prob α) (k : ℕ) (ω : Ω) : ℝ := P.F (R.w k ω)

def gradSq (R : Run P C prob α) (k : ℕ) (ω : Ω) : ℝ :=
  ‖gradient P.F (R.w k ω)‖ ^ 2

def expectedGradSq (R : Run P C prob α) (k : ℕ) : ℝ :=
  ∫ ω, gradSq R k ω ∂prob

def optimalValue (P : Objective d) : ℝ := sInf (Set.range P.F)

def expectedGap (R : Run P C prob α) (k : ℕ) : ℝ :=
  ∫ ω, P.F (R.w k ω) - optimalValue P ∂prob

def stepSum (α : ℕ → ℝ) (K : ℕ) : ℝ := ∑ k ∈ Finset.range K, α k

def weightedGradientSum (R : Run P C prob α) (K : ℕ) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.range K, α k * gradSq R k ω ∂prob

def gradientSum (R : Run P C prob α) (K : ℕ) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.range K, gradSq R k ω ∂prob

def fixedGapBound (P : Objective d) (C : MomentConstants)
    (w0 : Space d) (a c : ℝ) (k : ℕ) : ℝ :=
  a * P.L * C.M / (2 * c * C.μ) + (1 - a * c * C.μ) ^ k *
    (P.F w0 - optimalValue P - a * P.L * C.M / (2 * c * C.μ))

def diminishingGapConstant (P : Objective d) (C : MomentConstants)
    (w0 : Space d) (c β γ : ℝ) : ℝ :=
  max (β ^ 2 * P.L * C.M / (2 * (β * c * C.μ - 1)))
    ((γ + 1) * (P.F w0 - optimalValue P))

end BCN



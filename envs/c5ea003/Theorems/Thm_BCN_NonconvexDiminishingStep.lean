-- Prove2me | Theorems.Thm_BCN_NonconvexDiminishingStep
-- name    : BCN.NonconvexDiminishingStep
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-25T21:29:35.424536+00:00
-- url     : https://prove2.me/theorems/9d73f12b-c9d5-466a-87c9-6a265feb2146
-- title:
--   Theorem 4.10 — Nonconvex SG with Diminishing Step Sizes
-- statement:
--   ### Mathematical statement
--   No convexity assumption is made. Let the deterministic
--   positive step sizes satisfy
--   $$\sum_{k=0}^{\infty}\alpha_k=\infty,
--   \qquad\sum_{k=0}^{\infty}\alpha_k^2<\infty.$$
--   Then the expected weighted partial sums converge to a finite real number, and
--   their step-weighted averages vanish:
--   $$\exists S\in\mathbb R,\quad\lim_{K\to\infty}W_K=S,
--   \qquad\lim_{K\to\infty}\frac{W_K}{A_K}=0.$$
--   Formalization note: direct source theorem, both conclusions (4.30a)–(4.30b).
--   The existence of a finite limit formalizes the finite expectation limit in
--   (4.30a). It is stronger than merely asserting that each finite partial sum is
--   finite. There is no additional uniform upper bound on all step sizes, no
--   monotonicity requirement, and no assertion that every individual gradient tends
--   to zero. The objective lower bound is required on the open trajectory region.
--
--   Source: Léon Bottou, Frank E. Curtis, Jorge Nocedal, Optimization Methods for Large-Scale Machine Learning, arXiv:1606.04838v3, https://arxiv.org/abs/1606.04838v3; Section 4, PDF p. 33 and PDF p. 34, Theorem 4.10, equations (4.30a)–(4.30b); PDF p. 28, step-size condition (4.19).
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
--   Léon Bottou, Frank E. Curtis, Jorge Nocedal, Optimization Methods for Large-Scale Machine Learning, arXiv:1606.04838v3, https://arxiv.org/abs/1606.04838v3; Section 4, PDF p. 33 and PDF p. 34, Theorem 4.10, equations (4.30a)–(4.30b); PDF p. 28, step-size condition (4.19).

import Definitions.Def_BCN_SG_Model
open MeasureTheory Filter
open scoped Topology
universe u

namespace BCN
theorem NonconvexDiminishingStep :
  ∀ (d : ℕ) (P : Objective d) (C : MomentConstants)
    (Ω : Type u) [MeasurableSpace Ω] (prob : Measure Ω) [IsProbabilityMeasure prob]
    (α : ℕ → ℝ) (R : Run P C prob α),
    Tendsto (stepSum α) atTop atTop → Summable (fun k ↦ α k ^ 2) →
      (∃ S : ℝ, Tendsto (weightedGradientSum R) atTop (𝓝 S)) ∧
      Tendsto (fun K ↦ weightedGradientSum R K / stepSum α K) atTop (𝓝 0) := by sorry
end BCN

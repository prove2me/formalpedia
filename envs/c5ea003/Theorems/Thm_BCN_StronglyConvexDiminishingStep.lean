-- Prove2me | Theorems.Thm_BCN_StronglyConvexDiminishingStep
-- name    : BCN.StronglyConvexDiminishingStep
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-25T21:28:45.592691+00:00
-- url     : https://prove2.me/theorems/2c1180d6-a54d-42da-b274-de192533f506
-- title:
--   Theorem 4.7 — Strongly Convex SG with Diminishing Step Sizes
-- statement:
--   ### Mathematical statement
--   Assume $d\ge1$ and $F$ is $c$-strongly convex on all of
--   $\mathbb R^d$, with $c>0$. For differentiable $F$, this means
--   $$F(y)\ge F(x)+\nabla F(x)^\top(y-x)+\frac c2\|y-x\|^2
--   \quad\text{for all }x,y.$$
--   The Lean statement uses `StrongConvexOn Set.univ c F`. Set $F_{\inf}=F_*$,
--   where $F_*=\inf_x F(x)$ as defined above, and put $\Delta_0=F(w_0)-F_*$.
--
--   Choose real constants $\beta>1/(c\mu)$ and $\gamma>0$ such that
--   $\beta/(\gamma+1)\le\mu/(LM_G)$, and let
--   $\alpha_k=\beta/(\gamma+k+1)$. Define
--   $$\nu=\max\left\{\frac{\beta^2LM}{2(\beta c\mu-1)},
--   (\gamma+1)\Delta_0\right\}.$$
--   Then $\Delta_k\le\nu/(\gamma+k+1)$ for every $k\ge0$.
--   Formalization note: direct source theorem, with every index shifted consistently
--   from the paper's first index $1$ to the local first index $0$. The strict
--   conditions on $c$, $\beta$, and $\gamma$ make the displayed denominators positive.
--
--   Source: Léon Bottou, Frank E. Curtis, Jorge Nocedal, Optimization Methods for Large-Scale Machine Learning, arXiv:1606.04838v3, https://arxiv.org/abs/1606.04838v3; Section 4, PDF p. 28 and PDF p. 29, Theorem 4.7, equations (4.20)–(4.22).
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
--   Léon Bottou, Frank E. Curtis, Jorge Nocedal, Optimization Methods for Large-Scale Machine Learning, arXiv:1606.04838v3, https://arxiv.org/abs/1606.04838v3; Section 4, PDF p. 28 and PDF p. 29, Theorem 4.7, equations (4.20)–(4.22).

import Definitions.Def_BCN_SG_Model
open MeasureTheory Filter
open scoped Topology
universe u

namespace BCN
theorem StronglyConvexDiminishingStep :
  ∀ (d : ℕ), 0 < d → ∀ (P : Objective d) (C : MomentConstants)
    (Ω : Type u) [MeasurableSpace Ω] (prob : Measure Ω) [IsProbabilityMeasure prob]
    (c β γ : ℝ), 0 < c → StrongConvexOn Set.univ c P.F →
    1 / (c * C.μ) < β → 0 < γ → β / (γ + 1) ≤ C.μ / (P.L * C.MG) →
    ∀ R : Run P C prob (fun k ↦ β / (γ + (k : ℝ) + 1)),
      R.lower = optimalValue P → ∀ k,
        expectedGap R k ≤ diminishingGapConstant P C R.w0 c β γ / (γ + (k : ℝ) + 1) := by sorry
end BCN

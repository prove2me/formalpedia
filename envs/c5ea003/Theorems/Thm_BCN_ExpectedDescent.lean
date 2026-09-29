-- Prove2me | Theorems.Thm_BCN_ExpectedDescent
-- name    : BCN.ExpectedDescent
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-25T21:28:09.585976+00:00
-- url     : https://prove2.me/theorems/edd26ee4-1f18-4d4c-94d3-34640fdad95b
-- title:
--   Lemma 4.4 — Expected Descent
-- statement:
--   ### Mathematical statement
--   Under the common model assumptions, for every $k\ge0$,
--   both inequalities hold almost surely:
--   $$\begin{aligned}
--   \mathbb E[F(w_{k+1})\mid\mathcal F_k]-F(w_k)
--   &\le-\mu\alpha_k q_k+
--   \frac{\alpha_k^2L}{2}\mathbb E[\|g_k\|^2\mid\mathcal F_k]\\
--   &\le-\left(\mu-\frac{\alpha_kLM_G}{2}\right)\alpha_k q_k
--   +\frac{\alpha_k^2LM}{2}.
--   \end{aligned}$$
--   Formalization note: direct source theorem with full-history conditioning explicit.
--   No upper bound on the positive step size is needed for this lemma.
--
--   Source: Léon Bottou, Frank E. Curtis, Jorge Nocedal, Optimization Methods for Large-Scale Machine Learning, arXiv:1606.04838v3, https://arxiv.org/abs/1606.04838v3; Section 4, PDF p. 24 and PDF p. 25, Lemma 4.4, equations (4.10a)–(4.10b).
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
--   Léon Bottou, Frank E. Curtis, Jorge Nocedal, Optimization Methods for Large-Scale Machine Learning, arXiv:1606.04838v3, https://arxiv.org/abs/1606.04838v3; Section 4, PDF p. 24 and PDF p. 25, Lemma 4.4, equations (4.10a)–(4.10b).

import Definitions.Def_BCN_SG_Model
open MeasureTheory Filter
open scoped Topology
universe u

namespace BCN
theorem ExpectedDescent :
  ∀ (d : ℕ) (P : Objective d) (C : MomentConstants)
    (Ω : Type u) [MeasurableSpace Ω] (prob : Measure Ω) [IsProbabilityMeasure prob]
    (α : ℕ → ℝ) (R : Run P C prob α) (k : ℕ),
    (∀ᵐ ω ∂prob, prob[loss R (k + 1) | R.history k] ω - loss R k ω ≤
      -(C.μ * α k) * gradSq R k ω + α k ^ 2 * P.L / 2 *
        prob[(fun ω ↦ ‖R.g k ω‖ ^ 2) | R.history k] ω) ∧
    (∀ᵐ ω ∂prob,
      -(C.μ * α k) * gradSq R k ω + α k ^ 2 * P.L / 2 *
        prob[(fun ω ↦ ‖R.g k ω‖ ^ 2) | R.history k] ω ≤
      -(C.μ - α k * P.L * C.MG / 2) * α k * gradSq R k ω +
        α k ^ 2 * P.L * C.M / 2) := by sorry
end BCN

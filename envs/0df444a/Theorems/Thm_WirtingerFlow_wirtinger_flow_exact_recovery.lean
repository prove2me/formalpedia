-- Prove2me | Theorems.Thm_WirtingerFlow_wirtinger_flow_exact_recovery
-- name    : WirtingerFlow.wirtinger_flow_exact_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:58:05.14565+00:00
-- url     : https://prove2.me/theorems/476b243d-1dee-4b08-acbd-644b44e6a165
-- title:
--   Theorem 3.3 (as proved): exact phase retrieval via Wirtinger flow in the Gaussian model
-- statement:
--   There are numerical constants $c_0,\gamma,c_1>0$ with the following property. Let $a_1,\dots,a_m$ follow the Gaussian model, let $x\in\mathbb{C}^n$ be arbitrary, let $y=|Ax|^2$, and let $n\ge1$ and $m\ge c_0\,n\log n$.
--
--   1. With probability at least $1-10e^{-\gamma n}-8/n^2$, every Wirtinger flow initial estimate $z_0$ satisfies
--   $$\operatorname{dist}(z_0,x)\le\frac18\|x\|.\tag{3.1}$$
--   Here $z_0$ is a unit leading eigenvector of $Y=\frac1m\sum_ry_ra_ra_r^*$, rescaled to squared norm $m^{-1}\sum_ry_r$.
--   2. Let $0<\mu\le c_1/n$. Then there is an event of probability at least $1-13e^{-\gamma n}-me^{-1.5n}-8/n^2$ on which the following holds. For every $z_0$ obeying (3.1), the iterates $z_{\tau+1}=z_\tau-\frac{\mu}{\|z_0\|^2}\nabla f(z_\tau)$ satisfy, for all $\tau\ge0$,
--   $$\operatorname{dist}(z_\tau,x)\le\frac18\Big(1-\frac{\mu\|x\|^2}{4\|z_0\|^2}\Big)^{\tau/2}\|x\|.$$
--
--   So $m$ of order $n\log n$ phaseless Gaussian measurements suffice for a spectral initialization followed by Wirtinger flow to recover $x$, up to a global phase, at a geometric rate.
--
--   **Formalization Note** This is Theorem 3.3 in the form its proof establishes, in two respects.
--
--   1. The printed failure term $me^{-1.5m}$ is replaced by $me^{-1.5n}$. This is the probability that some $\|a_r\|$ exceeds $\sqrt{6n}$ (Section 7.1), an event the proof needs.
--   2. The printed contraction factor $1-\mu/4$ is replaced by $1-\mu\|x\|^2/(4\|z_0\|^2)$. The proof proves convergence for the step $\mu/\|x\|^2$ (eq. 7.1) and transfers it to the step $\mu/\|z_0\|^2$ by a rescaling. That rescaling changes the rate whenever $\|z_0\|\ne\|x\|$, and the bound $\|z_0\|^2\ge\frac{63}{64}\|x\|^2$ it invokes is not available for an arbitrary $z_0$ obeying (3.1).
--
--   The learning parameter is taken positive, as a step size. $(\cdot)^{\tau/2}$ is written as $\sqrt{(\cdot)^\tau}$.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 3.1, Theorem 3.3, eq. (3.1), p. 6; proof in Sections 7.1, 7.4-7.8, pp. 19-30

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem wirtinger_flow_exact_recovery :
    ∃ c0 γ c1 : ℝ, 0 < c0 ∧ 0 < γ ∧ 0 < c1 ∧
      ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → c0 * n * Real.log n ≤ m → ∀ x : Sig n,
        gaussModel m n {A | ¬ ∀ z0 ∈ initSet (rows A) (meas (rows A) x),
            phaseDist z0 x ≤ ‖x‖ / 8} ≤
          ENNReal.ofReal (10 * Real.exp (-γ * n) + 8 / (n : ℝ) ^ 2) ∧
        ∀ μ : ℝ, 0 < μ → μ ≤ c1 / n →
          gaussModel m n {A | ¬ ∀ z0 : Sig n, phaseDist z0 x ≤ ‖x‖ / 8 →
            ∀ τ : ℕ, phaseDist (wfSeq (rows A) (meas (rows A) x) μ z0 τ) x ≤
              1 / 8 * Real.sqrt ((1 - μ * ‖x‖ ^ 2 / (4 * ‖z0‖ ^ 2)) ^ τ) * ‖x‖} ≤
            ENNReal.ofReal (13 * Real.exp (-γ * n) + m * Real.exp (-1.5 * n) + 8 / (n : ℝ) ^ 2) := by sorry

end WirtingerFlow

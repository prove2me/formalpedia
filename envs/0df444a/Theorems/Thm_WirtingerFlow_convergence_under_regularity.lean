-- Prove2me | Theorems.Thm_WirtingerFlow_convergence_under_regularity
-- name    : WirtingerFlow.convergence_under_regularity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:42:11.139373+00:00
-- url     : https://prove2.me/theorems/37621c00-de8e-436d-9cf8-3564a92230f5
-- title:
--   Lemma 7.10: geometric convergence under the regularity condition
-- statement:
--   Let $a_1,\dots,a_m\in\mathbb{C}^n$ ($m\ge1$) and $x\in\mathbb{C}^n$, and let $f$ use the data $y=|Ax|^2$. Let $\alpha,\beta>0$ and suppose $f$ obeys $\mathrm{RC}(\alpha,\beta,\varepsilon)$. Let $z_0$ satisfy $\operatorname{dist}(z_0,x)\le\varepsilon$, let $0<\mu\le2/\beta$, and set $z_{\tau+1}=z_\tau-\mu\nabla f(z_\tau)$. Then for all $\tau\ge0$, $\operatorname{dist}(z_\tau,x)\le\varepsilon$ and
--
--   $$\operatorname{dist}^2(z_\tau,x)\le\Big(1-\frac{2\mu}{\alpha}\Big)^\tau\operatorname{dist}^2(z_0,x).$$
--
--   This is the deterministic engine of both convergence theorems. Once the regularity condition is established with high probability, geometric convergence follows.
--
--   **Formalization Note** Positivity of $\alpha$ and $\beta$ is implicit in the paper, which writes $1/\alpha$ and $1/\beta$. The condition $\mathrm{RC}$ is required for every phase attaining $\operatorname{dist}(z,x)$.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 7.4, Lemma 7.10, Condition 7.9, eqs. (7.10)-(7.11), p. 22

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem convergence_under_regularity {R : Type*} [Fintype R] [Nonempty R] {n : ℕ}
    (a : R → Sig n) (x : Sig n) (α β ε : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hRC : RegCond a x α β ε) (z0 : Sig n) (hz0 : phaseDist z0 x ≤ ε)
    (μ : ℝ) (hμ : 0 < μ) (hμβ : μ ≤ 2 / β) (τ : ℕ) :
    phaseDist (gdSeq a (meas a x) μ z0 τ) x ≤ ε ∧
      phaseDist (gdSeq a (meas a x) μ z0 τ) x ^ 2 ≤ (1 - 2 * μ / α) ^ τ * phaseDist z0 x ^ 2 := by sorry

end WirtingerFlow

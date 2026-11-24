-- Prove2me | Theorems.Thm_WirtingerFlow_cdp_wirtinger_flow_convergence
-- name    : WirtingerFlow.cdp_wirtinger_flow_convergence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:50:25.592836+00:00
-- url     : https://prove2.me/theorems/90c3d9f4-6f4f-4681-86fe-79b80350e246
-- title:
--   Theorem 5.1 (convergence part, as proved): Wirtinger flow converges geometrically in the coded diffraction model
-- statement:
--   There are numerical constants $c_0,c_1>0$ with the following property. Let the patterns $d_1,\dots,d_L$ have i.i.d. entries with an admissible law satisfying $|d|\le\sqrt6$ and $\mathbb E|d|^2=1$. Let $n\ge1$ and $L\ge c_0(\log n)^4$, let $x\in\mathbb{C}^n$, and let $0<\mu\le c_1$. Then there is an event of probability at least $1-(2L+1)/n^3-1/n^2$ on which the following holds. For every $z_0$ with
--
--   $$\operatorname{dist}(z_0,x)\le\frac1{8\sqrt n}\|x\|,$$
--
--   the Wirtinger flow iterates $z_{\tau+1}=z_\tau-\frac{\mu}{\|z_0\|^2}\nabla f(z_\tau)$ obey, for all $\tau\ge0$,
--
--   $$\operatorname{dist}(z_\tau,x)\le\frac1{8\sqrt n}\Big(1-\frac{\mu\|x\|^2}{15\|z_0\|^2}\Big)^{\tau/2}\|x\|.$$
--
--   **Formalization Note** This is the convergence half of Theorem 5.1 in the form its proof establishes. The proof gives the regularity condition with $\alpha=30$ (Section 7.6.1) and $\beta=550$ (Section 7.7). Lemma 7.10 applied with effective step $\mu\|x\|^2/\|z_0\|^2$ then yields the contraction factor $1-\mu\|x\|^2/(15\|z_0\|^2)$, not the printed $1-\mu/3$. The hypotheses $|d|\le\sqrt6$ (used in Section 7.1 to get $\|a_r\|\le\sqrt{6n}$) and $\mathbb E|d|^2=1$ are used by the proof but are not part of the paper's definition of admissibility. The initialization half (Algorithm 2) and the closing Gaussian-model sentence are not formalized.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 5, Theorem 5.1, eqs. (5.1)-(5.2), p. 16; proof in Sections 7.1, 7.4-7.7 (Section 7.6.1 for the curvature condition), pp. 19-28

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem cdp_wirtinger_flow_convergence :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
      ∀ ν : Measure ℂ, IsAdmissible ν (Real.sqrt 6) → ∫ d, ‖d‖ ^ 2 ∂ν = 1 →
      ∀ n L : ℕ, 1 ≤ n → 1 ≤ L → c0 * Real.log n ^ 4 ≤ L → ∀ x : Sig n,
      ∀ μ : ℝ, 0 < μ → μ ≤ c1 →
        cdpModel ν L n {d | ¬ ∀ z0 : Sig n, phaseDist z0 x ≤ ‖x‖ / (8 * Real.sqrt n) →
          ∀ τ : ℕ, phaseDist (wfSeq (cdpVecs d) (meas (cdpVecs d) x) μ z0 τ) x ≤
            1 / (8 * Real.sqrt n) *
              Real.sqrt ((1 - μ * ‖x‖ ^ 2 / (15 * ‖z0‖ ^ 2)) ^ τ) * ‖x‖} ≤
          ENNReal.ofReal ((2 * L + 1) / (n : ℝ) ^ 3 + 1 / (n : ℝ) ^ 2) := by sorry

end WirtingerFlow

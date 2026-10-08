-- Prove2me | Theorems.Thm_ZipkinLostSales_Variability_fbar_convexOn
-- name    : ZipkinLostSales.Variability.fbar_convexOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:50.22651+00:00
-- url     : https://prove2.me/theorems/ace03855-c952-4a56-9f9f-6f8ed670ec88
-- title:
--   Theorem 4, p. 939, with §3, p. 938 — the optimal lost-sales cost f̄_t(v) is convex on V
-- statement:
--   Consider the lost-sales model of Zipkin (2008) in the transformed state, with lead time $L\ge1$, costs $c,\hat h,p\ge0$, discount factor $0<\gamma\le1$, and one-period demand law $\mu$, a probability measure on $[0,\infty)$ with finite mean. Let $V=\{v\in\mathbb R^L: v_0\ge v_1\ge\dots\ge v_{L-1}\ge0\}$ be the state space and $\bar f_t$ the optimal cost functions of recursion (1)–(2).
--
--   Then for all $t$, $\bar f_t$ is convex on $V$:
--   $$\bar f_t(\lambda v+(1-\lambda)v')\le\lambda\bar f_t(v)+(1-\lambda)\bar f_t(v')\qquad(v,v'\in V,\ 0\le\lambda\le1).$$
--
--   The paper obtains this from Theorem 4 ($\bar f_t$ is L$^\natural$-convex) and its remark in §3 that L$^\natural$-convexity implies ordinary convexity. In the proof of Theorem 11, convexity of the continuation $\bar f_{t+1}$ is what makes $\bar\kappa_t$ jointly convex in $(v,\zeta,d)$.
--
--   **Formalization Note** The optimal cost is indexed by the number of periods to go $k$, with $\bar f=0$ at $k=0$; "for all $t$" is "for all $k$". The statement is for the model's $\bar f$ only, not a generic "L$^\natural$-convex implies convex", which fails without regularity. The conditions $c,\hat h,p\ge0$, $0<\gamma\le1$ read the paper's "unit cost" and "discount rate"; finite mean of demand is added so that $\hat q^0$ is finite.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), Theorem 4, and p. 938 (PDF p. 3), §3: "one can see that L♮-convexity also implies ordinary convexity"

import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Theorem 4 (Zipkin 2008, p. 939) with the remark of §3 (p. 938) that L♮-convexity implies
ordinary convexity, for the model's value functions: for one demand law `μ` and every number of
periods to go `k`, `f̄` is convex on the state space `V`. -/
theorem fbar_convexOn {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) :
    ∀ k : ℕ, ConvexOn ℝ (ZipkinLostSales.LNatural.V L) (ZipkinLostSales.LNatural.fbar c hh p γ μ k) := by sorry

end ZipkinLostSales.Variability

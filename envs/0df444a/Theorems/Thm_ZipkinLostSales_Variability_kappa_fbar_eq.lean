-- Prove2me | Theorems.Thm_ZipkinLostSales_Variability_kappa_fbar_eq
-- name    : ZipkinLostSales.Variability.kappa_fbar_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:41.208622+00:00
-- url     : https://prove2.me/theorems/34746fc5-1ed6-4cec-84ce-756ed55eb272
-- title:
--   Proof of Theorem 4, p. 939 — the optimal sales in (3) are a = min{d, v₀ − v₁}, so κ̄_t(v, ζ | d) = q̂(v₀ − v₁ − d) + γ f̄_{t+1}(v₊)
-- statement:
--   Consider the lost-sales model of Zipkin (2008) in the transformed state $v\in V$ (nonnegative vectors $v_0\ge v_1\ge\dots\ge v_{L-1}\ge0$, with $v_L=0$), with lead time $L\ge1$, costs $c,\hat h,p\ge0$, discount factor $0<\gamma\le1$, and one-period demand law $\mu$, a probability measure on $[0,\infty)$ with finite mean. Let $\bar f_{t+1}$ be an optimal cost function of the recursion (any number of periods to go), and let $\bar\kappa_t(v,\zeta\mid d)$ be the value of program (4) with continuation $\bar f_{t+1}$.
--
--   Then for every $v\in V$, every $\zeta\le0$ and every demand $d\ge0$, the choice $a=\min\{d,v_0-v_1\}$ (sell as much as possible) is optimal in program (3), that is, $v_+=[v_0-v_1-d]^++v_1$ is optimal in (4), and
--   $$\bar\kappa_t(v,\zeta\mid d)=\hat q(v_0-v_1-d)+\gamma\,\bar f_{t+1}\big(([v_0-v_1-d]^++v_1,\ v_2,\dots,v_{L-1},0)-\zeta e\big).$$
--
--   This identity is what makes the decision-before-demand problem (5), $\bar g_t(v,\zeta)=-\gamma^Lc\zeta+E_d[\bar\kappa_t(v,\zeta\mid d)]$, agree with the recursion (1). The paper remarks that it is "not hard, but also not essential for this argument"; it is the bridge between the recursion and the program in which the joint convexity of Theorem 11's proof is stated.
--
--   **Formalization Note** The optimal cost is indexed by the number of periods to go $k$ ("for all $t$" becomes "for all $k$"); `kappa` is program (4) as an infimum over $v_+\in[\max(v_0-d,v_1),v_0]$. The conditions $c,\hat h,p\ge0$, $0<\gamma\le1$ read the paper's "unit cost" and "discount rate"; finite mean of demand is not in the paper and is added so that $\hat q^0$ is finite. The statement is for the model's own $\bar f$: it is false for an arbitrary continuation function.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), proof of Theorem 4: "(It is not hard, but also not essential for this argument, to show that the optimal a = min{d, v₀ − v₁}.)", programs (3) and (4)

import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): in program (3)/(4) with continuation `f̄_{t+1}` the
optimal sales are `a = min{d, v₀ − v₁}`, so that `κ̄(v, ζ | d) = q̂(v₀ − v₁ − d) + γ f̄_{t+1}(v₊)`
with `v₊` the transition of p. 938. Stated for one demand law `μ` and every number of periods
to go `k`. -/
theorem kappa_fbar_eq {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) :
    ∀ k : ℕ, ∀ v ∈ ZipkinLostSales.LNatural.V L, ∀ ζ : ℝ, ζ ≤ 0 → ∀ d : ℝ, 0 ≤ d →
      ZipkinLostSales.LNatural.kappa hh p γ (ZipkinLostSales.LNatural.fbar c hh p γ μ k) d v ζ
        = ZipkinLostSales.LNatural.qhat hh p (ZipkinLostSales.LNatural.vext v 0 - ZipkinLostSales.LNatural.vext v 1 - d) + γ * ZipkinLostSales.LNatural.fbar c hh p γ μ k (ZipkinLostSales.LNatural.next v d ζ) := by sorry

end ZipkinLostSales.Variability

-- Prove2me | Theorems.Thm_ZipkinLostSales_Variability_theorem_11
-- name    : ZipkinLostSales.Variability.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:43.380981+00:00
-- url     : https://prove2.me/theorems/ccadcd30-fdff-4753-92f9-9a8cc51f7310
-- title:
--   Theorem 11, p. 941 — if d(φ) increases in φ in the convex order, the optimal lost-sales cost f̄_t(v; φ) is nondecreasing in φ
-- statement:
--   Consider the single-item lost-sales inventory model of Zipkin (2008) in the transformed state $v\in V=\{v\in\mathbb R^L:v_0\ge v_1\ge\dots\ge v_{L-1}\ge0\}$, with lead time $L\ge1$, procurement, holding and penalty costs $c,\hat h,p\ge0$, and discount factor $0<\gamma\le1$. Suppose the distribution of demand depends on a real parameter $\phi$: for each $\phi$, the one-period demand $d(\phi)$ has law $\mu_\phi$, a probability measure on $[0,\infty)$ with finite mean, and demands of different periods are independent with this law. Write $\bar f_t(v;\phi)$ for the optimal cost of recursion (1)–(2), in the state $v$, under demand law $\mu_\phi$.
--
--   Suppose $d(\phi)$ is increasing in $\phi$ with respect to the convex order: for $\phi\le\phi'$,
--   $$E\,g(d(\phi))\le E\,g(d(\phi'))\quad\text{for every convex } g:\mathbb R\to\mathbb R\text{ for which both expectations exist}.$$
--   Then for all $t$ and all $v\in V$,
--   $$\phi\le\phi'\ \Longrightarrow\ \bar f_t(v;\phi)\le\bar f_t(v;\phi').$$
--
--   In words, more variable demand (in the convex order, which keeps the mean fixed and does not decrease the variance) leads to higher optimal cost. The paper notes that this is known for systems with backorders and new in the lost-sales setting.
--
--   **Formalization Note** "For all $t$" is "for every number of periods to go $k$", with $\bar f=0$ at $k=0$; by stationarity this covers every period of every horizon. The parameter $\phi$ ranges over $\mathbb R$. The convex order is the platform definition `StochasticOrders.Convex.ConvexOrder` applied to the identity random variable on $(\mathbb R,\mu_\phi)$ and $(\mathbb R,\mu_{\phi'})$; equal means are not assumed separately. The paper's "min" over orders is an infimum over $\zeta=-z\le0$. The conditions $c,\hat h,p\ge0$ and $0<\gamma\le1$ read the paper's "unit cost" and "discount rate"; nonnegative demand is the paper's; finite mean of each $\mu_\phi$ is added so that the expected one-period cost $\hat q^0$ is finite.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 941 (PDF p. 6), Theorem 11

import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
import Definitions.Def_StochasticOrders_Convex_ConvexOrder
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Theorem 11 (Zipkin 2008, p. 941): if the demand `d(φ)`, with law `μ φ`, is increasing in
`φ` with respect to the convex order, then the optimal cost `f̄_t(v; φ)` is nondecreasing in `φ`
for all `t`, i.e. for every number of periods to go `k` and every state `v ∈ ZipkinLostSales.LNatural.V`. -/
theorem theorem_11 {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : ℝ → Measure ℝ)
    (hμprob : ∀ φ, IsProbabilityMeasure (μ φ)) (hμnonneg : ∀ φ, μ φ (Set.Iio 0) = 0)
    (hμint : ∀ φ, Integrable id (μ φ))
    (hcx : ∀ φ φ' : ℝ, φ ≤ φ' → StochasticOrders.Convex.ConvexOrder (μ φ) (μ φ') id id) :
    ∀ k : ℕ, ∀ v ∈ ZipkinLostSales.LNatural.V L, Monotone (fun φ : ℝ => ZipkinLostSales.LNatural.fbar c hh p γ (μ φ) k v) := by sorry

end ZipkinLostSales.Variability

-- Prove2me | Theorems.Thm_ZipkinLostSales_Variability_gbar_monotone
-- name    : ZipkinLostSales.Variability.gbar_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:26:00.943268+00:00
-- url     : https://prove2.me/theorems/65db6553-e7ea-4c76-8806-2768ccada514
-- title:
--   Proof of Theorem 11, p. 941 — if f̄_{t+1}(v; φ) is nondecreasing in φ, so is ḡ_t(v, ζ; φ)
-- statement:
--   Consider the lost-sales model of Zipkin (2008) in the transformed state, with lead time $L\ge1$, costs $c,\hat h,p\ge0$ and discount factor $0<\gamma\le1$. Suppose the demand distribution depends on a real parameter $\phi$: for each $\phi\in\mathbb R$, $d(\phi)$ has law $\mu_\phi$, a probability measure on $[0,\infty)$ with finite mean. Suppose $d(\phi)$ is increasing in $\phi$ in the convex order: for $\phi\le\phi'$,
--   $$E\,g(d(\phi))\le E\,g(d(\phi'))\quad\text{for every convex } g:\mathbb R\to\mathbb R \text{ for which both expectations exist.}$$
--   Write $\bar f_t(v;\phi)$ and $\bar g_t(v,\zeta;\phi)$ for the optimal cost functions of recursion (1)–(2) with demand law $\mu_\phi$.
--
--   Then for every period $t$: if $\bar f_{t+1}(v;\phi)$ is nondecreasing in $\phi$ for every $v\in V$, then
--   $$\phi\le\phi'\ \Longrightarrow\ \bar g_t(v,\zeta;\phi)\le\bar g_t(v,\zeta;\phi')\qquad\text{for every } v\in V,\ \zeta\le0.$$
--
--   This is the induction step of Theorem 11; with it, the infimum over $\zeta\le0$ carries the monotonicity to $\bar f_t$.
--
--   **Formalization Note** Time is indexed by the number of periods to go $k$: the hypothesis is about $\bar f$ with $k$ periods to go and the conclusion about $\bar g$ with continuation $\bar f$ at $k$, for every $k$. The convex order is the platform definition `StochasticOrders.Convex.ConvexOrder` applied to the identity random variable on $(\mathbb R,\mu_\phi)$ and $(\mathbb R,\mu_{\phi'})$. Equal means are a consequence of the convex order and are not assumed. The conditions $c,\hat h,p\ge0$, $0<\gamma\le1$ read the paper's "unit cost" and "discount rate"; finite mean of every $\mu_\phi$ is added so that $\hat q^0$ is finite.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 941 (PDF p. 6), proof of Theorem 11: "Assume that f̄_{t+1}(v; φ) is nondecreasing in φ. … Consequently, ḡ_t(v, ζ; φ) is nondecreasing in φ"

import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
import Definitions.Def_StochasticOrders_Convex_ConvexOrder
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Proof of Theorem 11 (Zipkin 2008, p. 941), the induction step: if the demand `d(φ)` with law
`μ φ` increases in `φ` in the convex order and `f̄_{t+1}(v; φ)` is nondecreasing in `φ` on `V`,
then `ḡ_t(v, ζ; φ)` is nondecreasing in `φ` for every `v ∈ ZipkinLostSales.LNatural.V` and `ζ ≤ 0`. Time is indexed by
the number of periods to go `k` (`gbar … k` has continuation `fbar … k`). -/
theorem gbar_monotone {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : ℝ → Measure ℝ)
    (hμprob : ∀ φ, IsProbabilityMeasure (μ φ)) (hμnonneg : ∀ φ, μ φ (Set.Iio 0) = 0)
    (hμint : ∀ φ, Integrable id (μ φ))
    (hcx : ∀ φ φ' : ℝ, φ ≤ φ' → StochasticOrders.Convex.ConvexOrder (μ φ) (μ φ') id id) :
    ∀ k : ℕ, (∀ v ∈ ZipkinLostSales.LNatural.V L, Monotone (fun φ : ℝ => ZipkinLostSales.LNatural.fbar c hh p γ (μ φ) k v)) →
      ∀ v ∈ ZipkinLostSales.LNatural.V L, ∀ ζ : ℝ, ζ ≤ 0 → Monotone (fun φ : ℝ => ZipkinLostSales.LNatural.gbar c hh p γ (μ φ) k v ζ) := by sorry

end ZipkinLostSales.Variability

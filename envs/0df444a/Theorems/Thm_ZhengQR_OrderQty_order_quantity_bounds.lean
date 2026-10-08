-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_order_quantity_bounds
-- name    : ZhengQR.OrderQty.order_quantity_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:54:24.411975+00:00
-- url     : https://prove2.me/theorems/6a3bb331-e8a8-4474-8aa6-180a0c9e2492
-- title:
--   Theorem 2 — $Q^*_d \le Q^* \le \bar Q$, $\bar Q \le \bar Q_1$, $\bar Q \le \bar Q_2$, and $\bar Q_1 - Q^*_d$ increases to a finite limit in $K$
-- statement:
--   Consider the continuous-review $(Q, r)$ inventory system with demand rate $\lambda > 0$, leadtime $L > 0$, holding cost rate $h > 0$ and backorder penalty rate $p > 0$. The leadtime demand $D$ has a distribution $\mu$ that is a probability measure, integrable, with mean $\mathbb{E}(D) = \lambda L$ and $D \ge 0$ almost surely, and the newsvendor cost $G(y) = \mathbb{E}[h(y-D)^+ + p(D-y)^+]$ has a unique minimizer $y^0$. Let $H(Q) = G(r(Q))$, where $r(Q)$ is the optimal reorder point for $Q$, and $H_0(Q) = H(Q) - G(y^0)$. In the EOQ model with the same parameters, $H_d(Q) = \frac{hp}{h+p}Q$ and $Q^*_d = \sqrt{2\lambda K(h+p)/(hp)}$.
--
--   For a fixed ordering cost $K > 0$, let $\bar Q$, $\bar Q_1$, $\bar Q_2$ be the positive solutions of
--
--   $$Q H_0(Q) = 2\lambda K, \qquad H_0(Q) = H_d(Q^*_d), \qquad \int_0^Q H_0(y)\,dy = \lambda K.$$
--
--   **(a)** Each of the three equations has exactly one positive solution, and for the optimal order quantity $Q^*$ of the stochastic model
--
--   $$Q^*_d \le Q^* \le \bar Q, \qquad \bar Q \le \bar Q_1, \qquad \bar Q \le \bar Q_2.$$
--
--   **(b)** Keep $\lambda, L, h, p, \mu$ fixed and let $K$ vary. Then $K \mapsto \bar Q_1(K) - Q^*_d(K)$ is nondecreasing on $(0, \infty)$, and it converges to a finite constant as $K \to \infty$.
--
--   So the EOQ quantity underestimates the optimal order quantity when demand is random, but the gap is at most $\bar Q_1 - Q^*_d$, which stays bounded as the ordering cost grows.
--
--   **Formalization Note** "$\bar Q \overset{\text{def}}{=} \{Q : \dots\}$" is read as the unique positive solution. The statement quantifies over any positive solutions and any optimal $Q^*$, and separately asserts that each equation has exactly one positive solution, so the bounds are not vacuous; existence and uniqueness of $Q^*$ is Lemma 6. Part (b) quantifies over every function $K \mapsto \bar Q_1(K)$ that solves the defining equation for each $K > 0$. The paper calls $\bar Q_1 - Q^*_d$ "an increasing function of $K$"; its proof shows a *nonnegative* derivative, so the claim proved and formalized is "nondecreasing". The limit is a real number, not $+\infty$. The four comparisons are exactly the paper's; $\bar Q_1$ and $\bar Q_2$ are not compared with each other.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 96, Theorem 2 (definitions of Q̄, Q̄₁, Q̄₂ in the display above it; proof pp. 96–97)

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Theorem 2 (Zheng 1992, p. 96). With `Q̄`, `Q̄₁`, `Q̄₂` the positive solutions of
`Q H₀(Q) = 2λK`, `H₀(Q) = H_d(Q*_d)` and `∫_0^Q H₀(y) dy = λK`:
(a) each of the three equations has exactly one positive solution, and for every optimal order
quantity `Q*`, `Q*_d ≤ Q* ≤ Q̄`, `Q̄ ≤ Q̄₁`, `Q̄ ≤ Q̄₂`;
(b) with `λ, L, h, p, μ` fixed, `K ↦ Q̄₁(K) - Q*_d(K)` is nondecreasing on `(0, ∞)` ("increasing")
and converges to a finite constant as `K → ∞`. -/
theorem order_quantity_bounds
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    (∀ K : ℝ, 0 < K →
      (∃! Q : ℝ, 0 < Q ∧ Q * H0fun (newsvendorCost h p μ) Q = 2 * lam * K) ∧
      (∃! Q : ℝ, 0 < Q ∧
        H0fun (newsvendorCost h p μ) Q = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) ∧
      (∃! Q : ℝ, 0 < Q ∧ (∫ y in (0 : ℝ)..Q, H0fun (newsvendorCost h p μ) y) = lam * K) ∧
      ∀ Qs Qb Qb1 Qb2 : ℝ,
        IsOptQty (newsvendorCost h p μ) lam K Qs →
        0 < Qb → Qb * H0fun (newsvendorCost h p μ) Qb = 2 * lam * K →
        0 < Qb1 →
        H0fun (newsvendorCost h p μ) Qb1 = Hfun (eoqCost lam L h p) (eoqQty lam K h p) →
        0 < Qb2 → (∫ y in (0 : ℝ)..Qb2, H0fun (newsvendorCost h p μ) y) = lam * K →
        eoqQty lam K h p ≤ Qs ∧ Qs ≤ Qb ∧ Qb ≤ Qb1 ∧ Qb ≤ Qb2) ∧
    ∀ Qb1 : ℝ → ℝ,
      (∀ K : ℝ, 0 < K → 0 < Qb1 K ∧
        H0fun (newsvendorCost h p μ) (Qb1 K) = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) →
      MonotoneOn (fun K => Qb1 K - eoqQty lam K h p) (Set.Ioi 0) ∧
      ∃ c : ℝ, Tendsto (fun K => Qb1 K - eoqQty lam K h p) atTop (𝓝 c) := by sorry

end ZhengQR.OrderQty

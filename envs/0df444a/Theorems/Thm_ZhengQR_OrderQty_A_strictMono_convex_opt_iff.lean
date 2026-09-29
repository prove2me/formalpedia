-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_A_strictMono_convex_opt_iff
-- name    : ZhengQR.OrderQty.A_strictMono_convex_opt_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:51:04.852354+00:00
-- url     : https://prove2.me/theorems/6fd1f9e0-890f-4c77-92bb-6ebfa5f29eb9
-- title:
--   Lemma 6 — $A$ is increasing convex, $Q = Q^*$ iff $A(Q) = \lambda K$, and $Q^*$ increases, $r^*$ decreases in $K$
-- statement:
--   Under the standing assumptions of the model ($\lambda, L, K, h, p > 0$; the leadtime demand distribution $\mu$ is a probability measure, integrable, with mean $\lambda L$ and nonnegative support; $G$ has a unique minimizer $y^0$), let $A(Q) = QH(Q) - \int_0^Q H(y)\,dy$ and $C(Q) = c(Q, r(Q))$. Then:
--
--   1. $A$ is strictly increasing and convex on $[0, \infty)$;
--   2. there is exactly one optimal order quantity $Q^*$, i.e. exactly one $Q > 0$ with $C(Q) \le C(Q')$ for all $Q' > 0$;
--   3. for every $Q > 0$,
--   $$Q = Q^* \iff A(Q) = \lambda K; \tag{10}$$
--   4. $Q^*$ is strictly increasing and the optimal reorder point $r^* = r(Q^*)$ is strictly decreasing in $K$: if $0 < K_1 < K_2$ and $Q_1$, $Q_2$ are the optimal order quantities for $K_1$, $K_2$, then $Q_1 < Q_2$ and $r(Q_2) < r(Q_1)$.
--
--   Equation (10) is the paper's characterization of the optimal order quantity, and it is what every comparison with the EOQ model runs through.
--
--   **Formalization Note** "Increasing" and "decreasing" are read strictly, as the paper's proof gives $A'(Q) = QH'(Q) > 0$ and Lemma 3 gives $r'(Q) < 0$. Existence and uniqueness of $Q^*$ (part 2) is implicit in the paper's "Let $Q^*$ be the optimal order quantity" and is stated explicitly. $\lambda$, $L$, $h$, $p$ and $\mu$ are the same for $K_1$ and $K_2$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 92, Lemma 6 and Eq. (10)

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Lemma 6 (Zheng 1992, p. 92): `A` is an increasing convex function on `[0, ∞)`; there is exactly
one optimal order quantity `Q*`, and for `Q > 0`, `Q = Q*` iff `A(Q) = λK` (Eq. (10)); `Q*` is
increasing and `r* = r(Q*)` is decreasing in `K` (all "increasing"/"decreasing" read strictly). -/
theorem A_strictMono_convex_opt_iff
    {lam L K h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    StrictMonoOn (Afun (newsvendorCost h p μ)) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (Afun (newsvendorCost h p μ)) ∧
    (∃! Q : ℝ, IsOptQty (newsvendorCost h p μ) lam K Q) ∧
    (∀ Q : ℝ, 0 < Q →
      (IsOptQty (newsvendorCost h p μ) lam K Q ↔ Afun (newsvendorCost h p μ) Q = lam * K)) ∧
    ∀ K₁ K₂ Q₁ Q₂ : ℝ, 0 < K₁ → K₁ < K₂ →
      IsOptQty (newsvendorCost h p μ) lam K₁ Q₁ → IsOptQty (newsvendorCost h p μ) lam K₂ Q₂ →
      Q₁ < Q₂ ∧ optReorder (newsvendorCost h p μ) Q₂ < optReorder (newsvendorCost h p μ) Q₁ := by sorry

end ZhengQR.OrderQty

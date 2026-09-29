-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_integral_A_chain
-- name    : ZhengQR.OrderQty.integral_A_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:53:57.276976+00:00
-- url     : https://prove2.me/theorems/6864e312-791e-4df5-b2ab-7c7cbd52c583
-- title:
--   Lemma 8 — $\int_0^Q H \ge \frac12 QH(Q) \ge A(Q) \ge \frac12 QH_0(Q) \ge \int_0^Q H_0$, with equality for deterministic demand
-- statement:
--   Under the standing assumptions of the model ($\lambda, L, h, p > 0$; the leadtime demand distribution $\mu$ is a probability measure, integrable, with mean $\lambda L$ and nonnegative support; $G$ has a unique minimizer $y^0$), for every $Q \ge 0$
--
--   $$\int_0^Q H(y)\,dy \;\ge\; \tfrac12 Q H(Q) \;\ge\; A(Q) \;\ge\; \tfrac12 Q H_0(Q) \;\ge\; \int_0^Q H_0(y)\,dy.$$
--
--   Moreover, when the leadtime demand is deterministic (the EOQ model, with cost rate $G_d(y) = h(y - \lambda L)^+ + p(\lambda L - y)^+$ and curves $H_d$, $A_d$, $H_{0,d} = H_d - G_d(y^0_d)$), all four inequalities hold as equalities for every $Q \ge 0$.
--
--   The chain compares the area under $H$ with the triangle under the chord, and is the tool behind the bounds on $Q^*$ in Theorem 2.
--
--   **Formalization Note** The paper states no range for $Q$; its proof fixes $Q > 0$, and $Q = 0$ adds only the trivial case $0 = 0$. "The leadtime demand is deterministic" is formalized as the model with cost rate $G_d$: by p. 94, the EOQ model is the stochastic model whose leadtime demand is the constant $\mathbb{E}(D) = \lambda L$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 95, Lemma 8

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Lemma 8 (Zheng 1992, p. 95): for every `Q ≥ 0`,
`∫_0^Q H(y) dy ≥ ½ Q H(Q) ≥ A(Q) ≥ ½ Q H₀(Q) ≥ ∫_0^Q H₀(y) dy`,
and all the inequalities hold as equalities when the leadtime demand is deterministic (the EOQ
model, cost rate `G_d`). -/
theorem integral_A_chain
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    (∀ Q : ℝ, 0 ≤ Q →
      1 / 2 * Q * Hfun (newsvendorCost h p μ) Q ≤ ∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y ∧
      Afun (newsvendorCost h p μ) Q ≤ 1 / 2 * Q * Hfun (newsvendorCost h p μ) Q ∧
      1 / 2 * Q * H0fun (newsvendorCost h p μ) Q ≤ Afun (newsvendorCost h p μ) Q ∧
      (∫ y in (0 : ℝ)..Q, H0fun (newsvendorCost h p μ) y) ≤ 1 / 2 * Q * H0fun (newsvendorCost h p μ) Q) ∧
    (∀ Q : ℝ, 0 ≤ Q →
      1 / 2 * Q * Hfun (eoqCost lam L h p) Q = ∫ y in (0 : ℝ)..Q, Hfun (eoqCost lam L h p) y ∧
      Afun (eoqCost lam L h p) Q = 1 / 2 * Q * Hfun (eoqCost lam L h p) Q ∧
      1 / 2 * Q * H0fun (eoqCost lam L h p) Q = Afun (eoqCost lam L h p) Q ∧
      (∫ y in (0 : ℝ)..Q, H0fun (eoqCost lam L h p) y) = 1 / 2 * Q * H0fun (eoqCost lam L h p) Q) := by sorry

end ZhengQR.OrderQty

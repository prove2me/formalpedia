-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_H_strictMono_convex_slope
-- name    : ZhengQR.OrderQty.H_strictMono_convex_slope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:50:35.013469+00:00
-- url     : https://prove2.me/theorems/7e438c33-2bf5-4bb5-8311-f5af20808633
-- title:
--   Lemma 4 — $H$ is increasing and convex on $[0, \infty)$ with asymptotic slope $hp/(h + p)$
-- statement:
--   Under the standing assumptions of the model ($\lambda, L, h, p > 0$; the leadtime demand distribution $\mu$ is a probability measure, integrable, with mean $\lambda L$ and nonnegative support; $G$ has a unique minimizer $y^0$), let $H(Q) = G(r(Q))$ for $Q > 0$ and $H(0) = G(y^0)$. Then:
--
--   1. $H$ is strictly increasing on $[0, \infty)$;
--   2. $H$ is convex on $[0, \infty)$;
--   3. $H$ has asymptotic slope $hp/(h+p)$:
--   $$\lim_{Q \to \infty} \frac{H(Q)}{Q} = \frac{hp}{h+p};$$
--   4. no chord of $H$ is steeper than that slope: for $0 \le Q < Q'$,
--   $$H(Q') - H(Q) \le \frac{hp}{h + p}\,(Q' - Q).$$
--
--   The slope $hp/(h+p)$ is exactly the slope of the EOQ model's $H_d$, which is why $H$ is compared with $H_d$ in the rest of the paper.
--
--   **Formalization Note** The paper writes "increasing"; its proof shows $H'(Q) > 0$, so the claim is read as *strictly* increasing. "Asymptotic slope $hp/(h+p)$" is read as the ratio limit (3) together with the chord bound (4), which is the derivative-free form of $H'(Q) \le hp/(h+p)$ that the paper uses in (23). The paper differentiates $G$ twice; no density is assumed here.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Lemma 4

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Lemma 4 (Zheng 1992, p. 91): `H` is an increasing convex function on `[0, ∞)` with asymptotic
slope `hp/(h + p)`. "Increasing" is read as strictly increasing; "asymptotic slope" as
`H(Q)/Q → hp/(h + p)` together with the chord bound `H(Q') - H(Q) ≤ hp/(h + p) (Q' - Q)` for
`0 ≤ Q < Q'` (the derivative-free form of `H' ≤ hp/(h + p)`, used by the paper in (23)). -/
theorem H_strictMono_convex_slope
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    StrictMonoOn (Hfun (newsvendorCost h p μ)) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (Hfun (newsvendorCost h p μ)) ∧
    Tendsto (fun Q => Hfun (newsvendorCost h p μ) Q / Q) atTop (𝓝 (h * p / (h + p))) ∧
    ∀ Q Q' : ℝ, 0 ≤ Q → Q < Q' →
      Hfun (newsvendorCost h p μ) Q' - Hfun (newsvendorCost h p μ) Q ≤
        h * p / (h + p) * (Q' - Q) := by sorry

end ZhengQR.OrderQty

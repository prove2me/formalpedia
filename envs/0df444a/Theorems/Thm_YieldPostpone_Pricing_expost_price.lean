-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_expost_price
-- name    : YieldPostpone.Pricing.expost_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:29.298738+00:00
-- url     : https://prove2.me/theorems/4b99a5d7-5cd9-44af-872a-da1e3cfb0d11
-- title:
--   (5), App. B, PDF p. 34 — the ex post price p*(q̂) is (a − q̂)/b for q̂ < a/2 and a/(2b) for q̂ > a/2
-- statement:
--   Under responsive pricing the retailer sets its price after observing the available quantity $\hat q$, maximizing its revenue $p\min\{d(p), \hat q\}$ with $d(p) = a - bp$ over prices $0 < p < a/b$. For admissible parameters ($a, b > 0$):
--   1. if $0 < \hat q < a/2$, the price $(a-\hat q)/b$ is admissible and is the unique maximizer;
--   2. if $\hat q > a/2$, the price $a/(2b)$ is admissible and is the unique maximizer.
--
--   In short,
--   $$p^*(\hat q) = \frac{a-\hat q}{b}\,\mathbf 1\{0<\hat q<a/2\} + \frac{a}{2b}\,\mathbf 1\{\hat q> a/2\}.$$
--   With little stock the retailer clears it; with ample stock it charges the monopoly price and leaves the rest unsold. This is the last stage of scenarios OR and DR.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. B, PDF p. 34 (appendix p. 2), (5)

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem expost_price (P : Params) (hP : P.Valid) (x : ℝ) :
    (0 < x → x < P.a / 2 →
      pAdm P ((P.a - x) / P.b) ∧
      ∀ p : ℝ, pAdm P p → p ≠ (P.a - x) / P.b →
        salesRev P p x < salesRev P ((P.a - x) / P.b) x) ∧
    (P.a / 2 < x →
      pAdm P (P.a / (2 * P.b)) ∧
      ∀ p : ℝ, pAdm P p → p ≠ P.a / (2 * P.b) →
        salesRev P p x < salesRev P (P.a / (2 * P.b)) x) := by sorry

end YieldPostpone.Pricing

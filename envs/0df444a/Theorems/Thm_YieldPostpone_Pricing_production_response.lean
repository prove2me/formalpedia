-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_production_response
-- name    : YieldPostpone.Pricing.production_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:31.782821+00:00
-- url     : https://prove2.me/theorems/f7f988d6-9465-474c-bcea-7a34996b21ef
-- title:
--   (4), App. B, PDF p. 33 — under pay-by-delivery the supplier produces q below w = c/(α(1−θ)) and inflates to q/α above it
-- statement:
--   Consider a pay-by-delivery scenario (DA or DR) with admissible parameters and cost $0 < c < a\mu/b$. Fix an admissible wholesale price $c/\mu < w < a/b$ and an order $q > 0$. The supplier's expected profit from producing $Q \ge 0$ is
--   $$\pi_S(Q) = -cQ + \theta w\min\{Q, q\} + (1-\theta) w\min\{\alpha Q, q\}.$$
--   Let $w_0 = c/(\alpha(1-\theta))$. Then:
--   1. if $w < w_0$, the unique maximizer of $\pi_S$ over $Q \ge 0$ is $Q = q$ (no inflation);
--   2. if $w > w_0$, the unique maximizer of $\pi_S$ over $Q \ge 0$ is $Q = q/\alpha$ (inflation).
--
--   This is the supplier's last-stage production response, the first step of the backward induction in every pay-by-delivery scenario.
--
--   **Formalization Note.** At $w = w_0$ every $Q \in [q, q/\alpha]$ is optimal; the paper's (4) assigns this tie to inflation, while the mission's equilibrium notion resolves it by $Q = q$ (see the Setting). This milestone states only the two strict cases, which do not depend on the tie rule.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. B, PDF p. 33 (appendix p. 1), (4)

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem production_response (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c)
    (hcμ : c < P.a * μ P / P.b) (k : Scenario) (hk : k.byDelivery = true)
    (w q : ℝ) (hw : wAdm P c k w) (hq : 0 < q) :
    (w < c / (P.α * (1 - P.θ)) →
      ∀ Q : ℝ, (0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q) ↔ Q = q) ∧
    (c / (P.α * (1 - P.θ)) < w →
      ∀ Q : ℝ, (0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q) ↔ Q = q / P.α) := by sorry

end YieldPostpone.Pricing

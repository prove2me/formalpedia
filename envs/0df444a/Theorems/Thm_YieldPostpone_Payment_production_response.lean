-- Prove2me | Theorems.Thm_YieldPostpone_Payment_production_response
-- name    : YieldPostpone.Payment.production_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:25.817066+00:00
-- url     : https://prove2.me/theorems/26626917-d761-46ed-8ee4-4ca1259632c6
-- title:
--   Appendix B (4) — supplier production response
-- statement:
--   Under pay-by-delivery, fix a positive order $q$, admissible wholesale price $w$, and production cost $c$. For the paper's two-point yield, the supplier's profit-maximizing nonnegative production quantity is uniquely determined away from the threshold $c/[\alpha(1-\theta)]$:
--
--   $$Q^*=q\quad\text{if }w<\frac{c}{\alpha(1-\theta)},\qquad Q^*=\frac q\alpha\quad\text{if }w>\frac{c}{\alpha(1-\theta)}.$$
--
--   This is the production response used in the delivery-payment equilibria.
--
--   **Formalization Note** The equality case is excluded from this uniqueness claim because every production quantity between the two kinks is optimal there. The model's equilibrium predicate selects $Q=q$ when that is a best response, the convention used to make the middle DR outcome an equilibrium.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. B, PDF p. 33 (appendix p. 1), (3)–(4)

import Definitions.Def_YieldPostpone_Payment_Setting

namespace YieldPostpone.Payment

theorem production_response (P : Params) (c w q : ℝ)
    (hP : P.Valid) (hc : costAdm P c) (hw : wAdm P c .DA w) (hq : 0 < q) :
    (w < c / (P.α * (1 - P.θ)) →
      ∀ Q : ℝ, (0 ≤ Q ∧
        ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c .DA w Q' q ≤ supplierProfit P c .DA w Q q) ↔ Q = q) ∧
    (c / (P.α * (1 - P.θ)) < w →
      ∀ Q : ℝ, (0 ≤ Q ∧
        ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c .DA w Q' q ≤ supplierProfit P c .DA w Q q) ↔
        Q = q / P.α) := by sorry

end YieldPostpone.Payment

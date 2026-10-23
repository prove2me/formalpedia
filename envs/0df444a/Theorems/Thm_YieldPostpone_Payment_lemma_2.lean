-- Prove2me | Theorems.Thm_YieldPostpone_Payment_lemma_2
-- name    : YieldPostpone.Payment.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:26.337832+00:00
-- url     : https://prove2.me/theorems/fb6c2b3c-7570-475d-8b7a-db20471cfc84
-- title:
--   Lemma 2 — OR equilibrium outcomes
-- statement:
--   For valid demand and yield parameters and each admissible cost $c$, scenario OR has a subgame-perfect equilibrium. Every equilibrium has the two-piece outcome in Appendix B.2:
--
--   $$c^{OR}<a\mu/b,\qquad (\pi_R^{OR},\pi_S^{OR},CS^{OR})=\begin{cases}F^{OR}_1,&0<c<\max\{0,c^{OR}\},\\F^{OR}_2,&\max\{0,c^{OR}\}<c<a\mu/b.\end{cases}$$
--
--   These formulas supply the pay-by-order baseline under responsive pricing.
--
--   **Formalization Note** The exact threshold is excluded from the outcome claim, while equilibrium existence is asserted there.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 11–12, Lemma 2; App. B.2, PDF p. 35 (appendix p. 3), Summary

import Definitions.Def_YieldPostpone_Payment_ClosedForms

namespace YieldPostpone.Payment

theorem lemma_2 (P : Params) (hP : P.Valid) :
    cOR P < P.a * P.μ / P.b ∧
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .OR σ) ∧
      (∀ σ : Profile, IsSPE P c .OR σ →
        (c < max 0 (cOR P) → outcome P c .OR σ = OR1 P c) ∧
        (max 0 (cOR P) < c → outcome P c .OR σ = OR2 P c)) := by sorry

end YieldPostpone.Payment

-- Prove2me | Theorems.Thm_YieldPostpone_Payment_lemma_3
-- name    : YieldPostpone.Payment.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:25.146052+00:00
-- url     : https://prove2.me/theorems/3057496b-f66f-4795-98a3-bf6d50517e09
-- title:
--   Lemma 3 — DA equilibrium outcomes
-- statement:
--   For valid demand and yield parameters and each admissible cost $c$, scenario DA has a subgame-perfect equilibrium. Every equilibrium has the two-piece outcome from Appendix B.3:
--
--   $$(\pi_R^{DA},\pi_S^{DA},CS^{DA})=\begin{cases}F^{DA}_1,&0<c<c^{DA},\\F^{DA}_2,&c^{DA}<c<a\mu/b.\end{cases}$$
--
--   The threshold $c^{DA}$ separates the two delivery-payment regimes under advance pricing. Its two formulas are recorded in ClosedForms.
--
--   **Formalization Note** The outcome at the threshold is excluded from the uniqueness claim, while equilibrium existence is asserted there.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 12, Lemma 3; App. B.3, PDF p. 36 (appendix p. 4), Summary

import Definitions.Def_YieldPostpone_Payment_ClosedForms

namespace YieldPostpone.Payment

theorem lemma_3 (P : Params) (hP : P.Valid) :
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .DA σ) ∧
      (∀ σ : Profile, IsSPE P c .DA σ →
        (c < cDA P → outcome P c .DA σ = DA1 P c) ∧
        (cDA P < c → outcome P c .DA σ = DA2 P c)) := by sorry

end YieldPostpone.Payment

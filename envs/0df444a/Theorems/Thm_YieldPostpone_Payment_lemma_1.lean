-- Prove2me | Theorems.Thm_YieldPostpone_Payment_lemma_1
-- name    : YieldPostpone.Payment.lemma_1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:22.434767+00:00
-- url     : https://prove2.me/theorems/831bc7af-b6a8-45de-a69c-0687d01d623c
-- title:
--   Lemma 1 — OA equilibrium outcomes
-- statement:
--   For valid demand and yield parameters and each admissible production cost $c$, scenario OA has a subgame-perfect equilibrium. Every such equilibrium has the outcome triple in Appendix B.1: $F^{OA}_1$ below $\max\{0,c^{OA}_1\}$, $F^{OA}_2$ between $\max\{0,c^{OA}_1\}$ and $\max\{0,c^{OA}_2\}$, and $F^{OA}_3$ above $\max\{0,c^{OA}_2\}$.
--
--   $$c^{OA}_1<c^{OA}_2<a\mu/b,\qquad (\pi_R^{OA},\pi_S^{OA},CS^{OA})=F^{OA}_j\quad\text{on the }j\text{th open cost interval}.$$
--
--   This identifies all three OA pieces needed to compare pay-by-order with pay-by-delivery under advance pricing.
--
--   **Formalization Note** The displayed closed forms are in the ClosedForms definition. Outcomes at exact cost thresholds are omitted because the source's uniqueness claim fails there; existence remains asserted for every admissible cost.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 10–11, Lemma 1; App. B.1, PDF pp. 34–35 (appendix pp. 2–3), Summary

import Definitions.Def_YieldPostpone_Payment_ClosedForms

namespace YieldPostpone.Payment

theorem lemma_1 (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * P.μ / P.b ∧
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      (∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) → outcome P c .OA σ = OA1 P c) ∧
        (max 0 (cOA1 P) < c ∧ c < max 0 (cOA2 P) →
          outcome P c .OA σ = OA2 P c) ∧
        (max 0 (cOA2 P) < c → outcome P c .OA σ = OA3 P c)) := by sorry

end YieldPostpone.Payment

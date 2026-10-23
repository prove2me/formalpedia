-- Prove2me | Theorems.Thm_YieldPostpone_Payment_lemma_1_corrected
-- name    : YieldPostpone.Payment.lemma_1_corrected
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T04:56:08.181287+00:00
-- url     : https://prove2.me/theorems/e90efc69-97f1-4b41-b470-36590108d7d7
-- title:
--   Lemma 1 (corrected middle-regime CS) — OA equilibrium outcomes
-- statement:
--   For valid demand and yield parameters ($a,b>0$, $0<\alpha<1$, $0<\theta<1$, $\mu=\alpha(1-\theta)+\theta$) and each admissible production cost $0<c<a\mu/b$, scenario OA (pay-by-order, ex ante pricing) has a subgame-perfect equilibrium, and every such equilibrium has the outcome triple $(\pi_R^{OA},\pi_S^{OA},CS^{OA})$ of Appendix B.1 on each open cost interval:
--
--   $$c^{OA}_1<c^{OA}_2<\frac{a\mu}{b},$$
--
--   - $F^{OA}_1$ (the ClosedForms value `OA1`) for $c<\max\{0,c^{OA}_1\}$;
--   - for $\max\{0,c^{OA}_1\}<c<\max\{0,c^{OA}_2\}$, with $\hat w$ the kink wholesale price of App. B.1,
--   $$\Big(\frac{(a\alpha-b\hat w)^2}{4b\alpha^2},\ \frac{(a\alpha-b\hat w)(\hat w-c)}{2\alpha^2},\ \frac{(a\alpha-b\hat w)^2}{8b\alpha^2}\Big);$$
--   - $F^{OA}_3$ (the ClosedForms value `OA3`) for $c>\max\{0,c^{OA}_2\}$.
--
--   **Correction note.** This is Lemma 1 of the source with one typo fixed. App. B.1 prints the middle-regime consumer surplus as $(a\alpha-b\hat w)^2/(8b\alpha^3)$, and the platform statement `YieldPostpone.Payment.lemma_1` (which uses that printed value through `ClosedForms.OA2`) was disproved. In the middle regime the retailer orders the inflated quantity $q=d/\alpha$ at price $p=(a/b+\hat w/\alpha)/2$, so both yield states sell $d=(a\alpha-b\hat w)/(2\alpha)$ and the consumer surplus is $d^2/(2b)=(a\alpha-b\hat w)^2/(8b\alpha^2)$. All other components are exactly as printed. Outcomes at the exact thresholds are omitted, as in the original platform statement, because uniqueness fails there; existence is asserted for every admissible cost.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 10–11, Lemma 1; App. B.1, PDF pp. 34–35 (appendix pp. 2–3), Summary (middle-regime CS denominator corrected from 8bα^3 to 8bα^2, see disproof of YieldPostpone.Payment.lemma_1)

import Definitions.Def_YieldPostpone_Payment_ClosedForms

namespace YieldPostpone.Payment

theorem lemma_1_corrected (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * P.μ / P.b ∧
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      (∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) → outcome P c .OA σ = OA1 P c) ∧
        (max 0 (cOA1 P) < c ∧ c < max 0 (cOA2 P) →
          outcome P c .OA σ =
            ((P.a * P.α - P.b * what P) ^ 2 / (4 * P.b * P.α ^ 2),
             (P.a * P.α - P.b * what P) * (what P - c) / (2 * P.α ^ 2),
             (P.a * P.α - P.b * what P) ^ 2 / (8 * P.b * P.α ^ 2))) ∧
        (max 0 (cOA2 P) < c → outcome P c .OA σ = OA3 P c)) := by sorry

end YieldPostpone.Payment

-- Prove2me | Theorems.Thm_YieldPostpone_Payment_lemma_4
-- name    : YieldPostpone.Payment.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:38.76815+00:00
-- url     : https://prove2.me/theorems/084a8858-ec03-4427-8718-00a17802c5d1
-- title:
--   Lemma 4 — DR equilibrium outcomes for mild yield loss
-- statement:
--   Suppose $\alpha\ge9/16$. For every admissible production cost $c$, scenario DR has a subgame-perfect equilibrium. Every equilibrium has one of three Appendix B.4 outcomes:
--
--   $$(\pi_R^{DR},\pi_S^{DR},CS^{DR})=\begin{cases}F^{DR}_1,&0<c<c^{DR}_1,\\F^{DR}_2,&c^{DR}_1<c<c^{DR}_2,\\F^{DR}_3,&c^{DR}_2<c<a\mu/b.\end{cases}$$
--
--   The result supplies all responsive-pricing delivery-payment outcomes used by Proposition 4(R).
--
--   **Formalization Note** The outcome statement uses open cost pieces because threshold outcomes need not be unique. On the middle piece, the supplier selects $Q=q$ when indifferent, and the consumer surplus formula is corrected consistently with that choice; the printed B.4 surplus uses a different production choice.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 13, Lemma 4; App. B.4, PDF p. 37 (appendix p. 5), Summary

import Definitions.Def_YieldPostpone_Payment_ClosedForms

namespace YieldPostpone.Payment

theorem lemma_4 (P : Params) (hP : P.Valid) (hα : (9 : ℝ) / 16 ≤ P.α) :
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .DR σ) ∧
      (∀ σ : Profile, IsSPE P c .DR σ →
        (c < cDR1 P → outcome P c .DR σ = DR1 P c) ∧
        (cDR1 P < c ∧ c < cDR2 P → outcome P c .DR σ = DR2 P c) ∧
        (cDR2 P < c → outcome P c .DR σ = DR3 P c)) := by sorry

end YieldPostpone.Payment

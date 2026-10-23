-- Prove2me | Theorems.Thm_YieldPostpone_Payment_proposition_4
-- name    : YieldPostpone.Payment.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:29.711662+00:00
-- url     : https://prove2.me/theorems/dc790dab-a3fa-4776-905e-2e7837f8cc2f
-- title:
--   Proposition 4 — payment postponement and the whole chain
-- statement:
--   Let a supplier and retailer face the two-point yield and linear-demand game of the Setting definition. Compare switching from pay-by-order to pay-by-delivery while keeping the pricing rule fixed. For every admissible cost, equilibria exist in both scenarios being compared, and the claims below hold for every pair of equilibrium profiles.
--
--   Under ex ante pricing (OA to DA), for every $0<\alpha<1$, $0<\overline C<c^{DA}$. The changes in retailer profit, supplier profit, and consumer surplus, respectively, have signs
--
--   $$\begin{array}{c|c}\text{cost interval}&(\Delta\pi_R,\Delta\pi_S,\Delta CS)\\(\max\{0,c^{OA}_2\},\max\{\overline C,c^{OA}_2\}) &(+,+,+)\\(\max\{\overline C,c^{OA}_2\},c^{DA}) &(+,+,-)\\(0,\max\{0,c^{OA}_1\})\ \text{or}\ (c^{DA},a\mu/b)&(0,0,0).\end{array}$$
--
--   Under responsive pricing (OR to DR), assume additionally $\alpha\ge9/16$. The sign pattern is $(+,+,+)$ on $(0,\widetilde C)$, $(-,-,-)$ on $(\widetilde C,c^{DR}_1)$, $(+,-,+)$ on $(c^{DR}_1,c^{DR}_2)$, and $(0,0,0)$ on $(c^{DR}_2,a\mu/b)$. Every plus or minus is strict; zero means equality.
--
--   This establishes when shifting yield risk upstream benefits or harms the retailer, supplier, and consumers.
--
--   **Formalization Note** The thresholds $\overline C$ and $\widetilde C$ use the paper's explicit formulas (8) and (6). The middle DR consumer surplus uses the equilibrium-consistent correction described in ClosedForms; the comparison on $(c^{DR}_1,c^{DR}_2)$ holds under both the corrected and printed values. The statement includes equilibrium existence so its comparisons are nonvacuous.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 19–20, Proposition 4(A), (R); App. C, PDF pp. 37–38 (appendix pp. 5–6), (6), (8), proof of Proposition 4

import Definitions.Def_YieldPostpone_Payment_ClosedForms

namespace YieldPostpone.Payment

theorem proposition_4 (P : Params) (hP : P.Valid) :
    (0 < Cbar P ∧ Cbar P < cDA P ∧
      (∀ c, costAdm P c →
        (∃ σ : Profile, IsSPE P c .OA σ) ∧
        (∃ σ : Profile, IsSPE P c .DA σ)) ∧
      (∀ c σOA σDA, costAdm P c →
        IsSPE P c .OA σOA → IsSPE P c .DA σDA →
        (max 0 (cOA2 P) < c ∧ c < max (Cbar P) (cOA2 P) →
          piR P c .OA σOA < piR P c .DA σDA ∧
          piS P c .OA σOA < piS P c .DA σDA ∧
          CS P c .OA σOA < CS P c .DA σDA) ∧
        (max (Cbar P) (cOA2 P) < c ∧ c < cDA P →
          piR P c .OA σOA < piR P c .DA σDA ∧
          piS P c .OA σOA < piS P c .DA σDA ∧
          CS P c .DA σDA < CS P c .OA σOA) ∧
        ((c < max 0 (cOA1 P)) ∨ (cDA P < c) →
          piR P c .OA σOA = piR P c .DA σDA ∧
          piS P c .OA σOA = piS P c .DA σDA ∧
          CS P c .OA σOA = CS P c .DA σDA))) ∧
    ((9 : ℝ) / 16 ≤ P.α →
      (∀ c, costAdm P c →
        (∃ σ : Profile, IsSPE P c .OR σ) ∧
        (∃ σ : Profile, IsSPE P c .DR σ)) ∧
      (∀ c σOR σDR, costAdm P c →
        IsSPE P c .OR σOR → IsSPE P c .DR σDR →
        (c < Ctil P →
          piR P c .OR σOR < piR P c .DR σDR ∧
          piS P c .OR σOR < piS P c .DR σDR ∧
          CS P c .OR σOR < CS P c .DR σDR) ∧
        (Ctil P < c ∧ c < cDR1 P →
          piR P c .DR σDR < piR P c .OR σOR ∧
          piS P c .DR σDR < piS P c .OR σOR ∧
          CS P c .DR σDR < CS P c .OR σOR) ∧
        (cDR1 P < c ∧ c < cDR2 P →
          piR P c .OR σOR < piR P c .DR σDR ∧
          piS P c .DR σDR < piS P c .OR σOR ∧
          CS P c .OR σOR < CS P c .DR σDR) ∧
        (cDR2 P < c →
          piR P c .OR σOR = piR P c .DR σDR ∧
          piS P c .OR σOR = piS P c .DR σDR ∧
          CS P c .OR σOR = CS P c .DR σDR))) := by sorry

end YieldPostpone.Payment

-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
-- name    : Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:54:05.746274+00:00
-- url     : https://prove2.me/theorems/2fab4d3e-ec99-4029-a3d7-7ea467931ba0
-- title:
--   Charge divisibility gives the signed medium-prime target ledger
-- statement:
--   Let $R$ be a bank realization with guarded anchor certificate of depth $d$. Assume $2d+1\le W<p$, $p$ prime, and the charge of the fixed exceptional factors divides the precharged tail target. Let $T$ be the resulting selector-tail target, $U$ the upper block, $E$ its exceptional factors, $D$ the exceptional donor set, and $B$ the precharge base state. Then
--
--   $$v_p(T)=\sum_{a\in U}v_p(a)-\sum_{a\in E}v_p(a)+\sum_{a\in D}v_p(a)-\sum_{a\in B}v_p(a).$$
--
--   This supplies the exact sign ledger at medium primes needed to compare selector moments with the tail target.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedResidualSelectorIdentification.lean#L619-L790

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd :
∀ {c : Real} {depth n W p : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (deltaStar : Real),
  LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)) W →
    Nat.Prime p →
      LT.lt.{0} W p →
        Dvd.dvd.{0}
            (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R
              (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
            (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate) →
          Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSignedResidualTargetLedger R certificate deltaStar
            p := by sorry

-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_roughCanonicalAggregateGuardResidual_le_majorant
-- name    : Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalAggregateGuardResidual_le_majorant
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:51:55.408871+00:00
-- url     : https://prove2.me/theorems/52a190fe-430f-4860-9382-b56eef9e9911
-- title:
--   Finite majorant for the complete aggregate guard residual
-- statement:
--   Let $R$ be a bank realization at endpoint $2n+h$ with guarded central-anchor certificate of depth $d$. Suppose raw weights lie in $[0,1]$ on the raw candidate set. Assume $2\le W$, $2d+1\le W<p\le Y$, $p$ prime, $Y$ below the central-anchor cutoff, and $2n+h\le3n$. Let $B_n=\mathrm{bankPaperAnchorMarkerBudget}(n)$. Then
--
--   $$|\mathrm{roughCanonicalAggregateGuardResidual}(R,p)|\le(2+4B_n)\,\lfloor\log_2(3n)\rfloor.$$
--
--   No signed cancellation or exceptional-charge estimate is needed for this guard contribution.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedGuardResidual.lean#L472-L599

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

theorem Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalAggregateGuardResidual_le_majorant :
∀ {c : Real} {depth n h W K p : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat}
  (R : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n h))
  (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed) (deltaStar : Real)
  (rawWeight : Nat → Real),
  (∀ (a : Nat),
      Membership.mem.{0, 0} (Erdos390.WholePaper.roughRawCandidateSet n h K) a →
        And (LE.le.{0} (0 : Real) (rawWeight a)) (LE.le.{0} (rawWeight a) (1 : Real))) →
    LE.le.{0} (2 : Nat) W →
      LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)) W →
        LT.lt.{0} W p →
          LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
            LT.lt.{0} (Erdos390.Full.ArithmeticModel.yNat n) (Erdos390.WholePaper.centralAnchorCutoff depth n) →
              Nat.Prime p →
                LE.le.{0} (Erdos390.WholePaper.upperEndpoint n h) (HMul.hMul.{0, 0, 0} (3 : Nat) n) →
                  LE.le.{0}
                    (abs.{0}
                      (Erdos390.WholePaper.BankPaperRealization.roughCanonicalAggregateGuardResidual R certificate
                        deltaStar K rawWeight p))
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalAggregateGuardResidualMajorant n) := by sorry

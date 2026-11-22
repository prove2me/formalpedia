-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:18:16.603748+00:00
-- url     : https://prove2.me/theorems/29940ffd-5dd5-4d09-a57b-482673e183fe
-- title:
--   The physical mixture budget gains one reciprocal marked prime
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, and $\mathcal P=\{p\text{ prime}:W<p\le Y\}$. Let $\epsilon,G\ge0$, $8\epsilon\le1$, $W>1$, and $p\in\mathcal P$. Let $B(\epsilon,G,n,W,p)$ be the explicitly defined physical power-correction mixture budget, and let $Q$ denote the fixed quadratic half-mass constant. Then
--
--   $$B(\epsilon,G,n,W,p)\le\frac1p\,200(8\epsilon)(1+Q)(1+G)^2\left(\sum_{q\in\mathcal P}\frac1q+1\right)\frac1W.$$
--
--   This finite contraction turns the mixture budget into the public weighted-row error without changing component weights.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalPowerCorrectionRow.lean#L202-L362

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError :
∀ {epsilon G : Real} {n W p : Nat},
  LE.le.{0} (0 : Real) epsilon →
    LE.le.{0} (HMul.hMul.{0, 0, 0} (8 : Real) epsilon) (1 : Real) →
      LE.le.{0} (0 : Real) G →
        LT.lt.{0} (1 : Nat) W →
          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
            LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget epsilon G n W p)
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p)
                (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionRowError epsilon G n W)) := by sorry

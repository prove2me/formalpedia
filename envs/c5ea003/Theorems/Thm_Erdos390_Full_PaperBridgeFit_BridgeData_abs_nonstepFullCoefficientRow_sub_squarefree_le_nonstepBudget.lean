-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:11:26.369219+00:00
-- url     : https://prove2.me/theorems/f1a60acb-f62a-482b-9206-02074e6feed4
-- title:
--   Exact prime-power budget for a non-step slow row
-- statement:
--   Let B be bridge data and let law be any bounded valuation law on a finite space. Suppose Cpow,ε,w≥0, W>1, the law satisfies the Lemma 7.5 prime-power transfer bounds with constants Cpow,ε, and the prime deviation L¹ sum is at most 7w. For each band i, write α_i for its center and D_i for its normalized local reciprocal-square deviation. The literal full and squarefree non-step coefficient rows satisfy the exact estimate below. The local diagonal is retained rather than bounded by a global cutoff tail.
--
--   $$|R_{\rm full}(i)-R_{\rm sf}(i)|\le \frac{21C_{\rm pow}}Ww\alpha_i+\frac{21\varepsilon}Ww+3(C_{\rm pow}+\varepsilon)D_i.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperNonstepSlowRightLedger.lean#L159-L688

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2 u_3

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {Omega : Type u_3} [inst_4 : Fintype.{u_3} Omega]
  {Mlaw : Nat} (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_3} Omega Mlaw) {Cpow epsilon w : Real},
  LE.le.{0} (0 : Real) Cpow →
    LE.le.{0} (0 : Real) epsilon →
      LE.le.{0} (0 : Real) w →
        LT.lt.{0} (1 : Nat)
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
          Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_3} law
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              Cpow epsilon →
            LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
                (HMul.hMul.{0, 0, 0} (7 : Real) w) →
              ∀ (i : Band),
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepFullCoefficientRow.{u_1, u_2, u_3} B law i)
                      (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepSquarefreeCoefficientRow.{u_1, u_2, u_3} B law
                        i)))
                  (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepPrimePowerRowBudget Cpow epsilon w
                    (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandDeviationReciprocalSquare.{u_1, u_2} B i)) := by sorry

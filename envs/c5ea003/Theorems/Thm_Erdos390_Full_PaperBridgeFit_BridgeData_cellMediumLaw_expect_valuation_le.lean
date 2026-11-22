-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_cellMediumLaw_expect_valuation_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw_expect_valuation_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:17:35.070082+00:00
-- url     : https://prove2.me/theorems/b80c05f9-3a97-45fd-ac2f-69632243677a
-- title:
--   A reciprocal first moment for the medium-law valuation
-- statement:
--   Let $B$ have nonempty head set, fix a cell $c$ and tilt parameter $\xi$, and let $p$ be prime. Assume $A\ge0$, $W>1$, $\rho>0$, cell size at least $\rho\,\mathrm{hi}_c$, and every effective prime coefficient bounded by $A$. Define $$G=\frac1\rho\exp\!\left(2\frac A{B.L}\frac{\log\mathrm{hi}_c}{\log W}\right).$$ Then
--
--   $$\mathbb E_{\mathrm{cellMediumLaw}}v_p(m)\le\frac{2G}{p}.$$
--
--   This reciprocal first moment is the marked input for covariance estimates involving the physical statistic.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalValuationRow.lean#L51-L165

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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw_expect_valuation_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) {rho A : Real} {p : Nat},
  Nat.Prime p →
    LE.le.{0} (0 : Real) A →
      LT.lt.{0} (1 : Nat)
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
        LT.lt.{0} (0 : Real) rho →
          LE.le.{0}
              (HMul.hMul.{0, 0, 0} rho
                ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c.2))
              ↑(Finset.card.{0}
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c)) →
            (∀
                (r :
                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                LE.le.{0}
                  (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} B xi r)) A) →
              have G :=
                HDiv.hDiv.{0, 0, 0}
                  (Real.exp
                    (HMul.hMul.{0, 0, 0} (2 : Real)
                      (HMul.hMul.{0, 0, 0}
                        (HDiv.hDiv.{0, 0, 0} A (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B))
                        (HDiv.hDiv.{0, 0, 0}
                          (Real.log
                            ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c.2))
                          (Real.log
                            ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))))
                  rho;
              LE.le.{0}
                (Erdos390.Full.FiniteProbability.expect.{0}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c) fun m =>
                  Erdos390.Full.ArithmeticModel.valuation p ↑m)
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) G) (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p)) := by sorry

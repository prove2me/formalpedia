-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualSquarefreeProjectedCLM_sub_arithmetic_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeProjectedCLM_sub_arithmetic_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:13:30.000985+00:00
-- url     : https://prove2.me/theorems/0b6c7341-6663-498d-88d9-804cd0182663
-- title:
--   Sharp-row comparison yields a projected operator comparison
-- statement:
--   Let $B$ be bridge data with nonempty head set, $\xi$ a parameter, and an interval certificate for its prime-band partition. Assume $r\ge0$ and that for every band vector $v$ with $|v_j|\le1$, every squarefree sharp row differs from the corresponding arithmetic sharp row by at most $r$. Let $A_\xi$ be the actual projected squarefree operator and $A_{\rm arith}$ the arithmetic projected sharp operator using the same centers and sharp weights. Then every vector $q$ in the sharp gauge space satisfies
--   $$\|(A_\xi-A_{\rm arith})q\|\le2r\|q\|.$$
--   The projection cost is independent of the number of bands and of the moving-low mass.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualSquarefreeReference.lean#L1497-L1621

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeProjectedCLM_sub_arithmetic_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (cert :
    Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_2}
      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
  {r : Real},
  LE.le.{0} (0 : Real) r →
    (∀ (q : Band → Real),
        (∀ (j : Band), LE.le.{0} (abs.{0} (q j)) (1 : Real)) →
          ∀ (i : Band),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeSharpRow.{u_1, u_2}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) q i)
                  (Erdos390.Full.CompressedArithmeticOperator.arithmeticSharpOperator.{u_2}
                    (Erdos390.Full.ArithmeticModel.y
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert)
                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                    q i)))
              r) →
      ∀
        (q :
          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
        LE.le.{0}
          (Norm.norm.{u_2}
            ((HSub.hSub.{u_2, u_2, u_2}
                (Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeProjectedCLM.{u_1, u_2} B xi)
                (Erdos390.Full.ArithmeticGaugeStableInverse.projectedSharpCLM.{u_2}
                  (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_2}
                    (Erdos390.Full.ArithmeticModel.y
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                  (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_2}
                    (Erdos390.Full.ArithmeticModel.y
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                  (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                  (ne_of_gt.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualSharpWeightTotal_pos.{u_1, u_2} B))))
              q))
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) r) (Norm.norm.{u_2} q)) := by sorry

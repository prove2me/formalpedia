-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_squarefreeSlowRow_sub_referenceSlowRow_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_squarefreeSlowRow_sub_referenceSlowRow_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:11:03.155777+00:00
-- url     : https://prove2.me/theorems/12807c29-4433-426b-9438-9868b9a6d8ce
-- title:
--   Entrywise aggregation for the squarefree slow row
-- statement:
--   Let B have a nonempty head type and fix a tilt ξ. Suppose ε_off,ε_diag≥0 and its indicator covariance entries differ from the squarefree reference by at most ε_off/(pq), plus on p=q the diagonal term ε_diag/p+Cdiag/p². If the prime deviation L¹ sum is at most 7w, then for each band i the normalized squarefree slow-score row differs from the reference slow row by the bound below. Here α_i is the band center and D_i its normalized reciprocal-square deviation.
--
--   $$|R_{\rm sf}(\xi,i)-R_{\rm ref}(i)|\le7\varepsilon_{\rm off}w+2\varepsilon_{\rm diag}\alpha_i+C_{\rm diag}D_i.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperNonstepSquarefreeSlowLedger.lean#L51-L279

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_squarefreeSlowRow_sub_referenceSlowRow_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B) {epsilonOff epsilonDiag Cdiag w : Real},
  LE.le.{0} (0 : Real) epsilonOff →
    LE.le.{0} (0 : Real) epsilonDiag →
      (∀
          (p q :
            Erdos390.Full.ArithmeticBandGeometry.BandPrime
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
          LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0}
                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q)
                (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  ↑p ↑q)))
            (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonOff (HMul.hMul.{0, 0, 0} ↑↑p ↑↑q))
              (ite.{1} (Eq.{1} p q)
                (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonDiag ↑↑p)
                  (HDiv.hDiv.{0, 0, 0} Cdiag (HPow.hPow.{0, 0, 0} ↑↑p (2 : Nat))))
                (0 : Real)))) →
        LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
            (HMul.hMul.{0, 0, 0} (7 : Real) w) →
          ∀ (i : Band),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedSquarefreeBandCovarianceRow.{u_1, u_2} B xi
                    (Erdos390.Full.PaperBridgeFit.BridgeData.slowSquarefreeScore.{u_1, u_2} B) i)
                  (Erdos390.Full.PaperBridgeFit.BridgeData.referenceSlowRow.{u_1, u_2} B i)))
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (7 : Real) epsilonOff) w)
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) epsilonDiag)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)))
                (HMul.hMul.{0, 0, 0} Cdiag
                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandDeviationReciprocalSquare.{u_1, u_2} B i))) := by sorry

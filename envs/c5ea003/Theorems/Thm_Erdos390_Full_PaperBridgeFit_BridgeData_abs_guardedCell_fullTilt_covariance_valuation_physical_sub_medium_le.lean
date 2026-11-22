-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:11:34.967923+00:00
-- url     : https://prove2.me/theorems/eebc716b-b0c7-41fd-b6e4-259cb7cfd0cf
-- title:
--   Residual physical tilt changes a marked valuation covariance by a logarithmic error
-- statement:
--   Let $B$ have nonempty head set and its cell endpoints equal the physical floors associated with intervals $I$, whose lower endpoints are at least one and upper endpoints at most $U$. Fix a cell, tilt parameter, and natural $p>0$. Suppose $A_p,A_v\ge0$, the physical tilt coordinate has absolute value at most $A_p$, the medium law satisfies $\mathbb E v_p\le A_v/p$, and $8A_p\log U/B.L\le1$. Let $R$ denote the physical score. Then
--
--   $$|\operatorname{Cov}_{\rm full\ cell}(v_p,R)-\operatorname{Cov}_{\rm medium\ cell}(v_p,R)|\le32\log U\,\frac{A_p\log U}{B.L}\,\frac{A_v}{p}.$$
--
--   The comparison retains both the marked-prime factor and the inverse logarithmic ambient scale.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalValuationRow.lean#L662-L796

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals)
  {U Aphys Aval : Real} {p : Nat},
  LT.lt.{0} (0 : Nat) p →
    LE.le.{0} (0 : Real) Aphys →
      LE.le.{0} (0 : Real) Aval →
        (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
            LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)) →
          (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
              LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U) →
            (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                Eq.{1}
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                  (Erdos390.Full.ArithmeticModel.physicalBound
                    (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))) →
              (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                  Eq.{1}
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                    (Erdos390.Full.ArithmeticModel.physicalBound
                      (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))) →
                LE.le.{0}
                    (abs.{0}
                      (WithLp.ofLp.{max u_1 u_2} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}))
                    Aphys →
                  LE.le.{0}
                      (Erdos390.Full.FiniteProbability.expect.{0}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c) fun m =>
                        Erdos390.Full.ArithmeticModel.valuation p ↑m)
                      (HDiv.hDiv.{0, 0, 0} Aval ↑p) →
                    LE.le.{0}
                        (HMul.hMul.{0, 0, 0} (8 : Real)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys (Real.log U))
                            (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B)))
                        (1 : Real) →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.covariance.{0}
                              (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c)
                                (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c))
                              (fun m => Erdos390.Full.ArithmeticModel.valuation p ↑m) fun m =>
                              Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} B
                                (Sigma.mk.{u_1, 0} c m))
                            (Erdos390.Full.FiniteProbability.covariance.{0}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c)
                              (fun m => Erdos390.Full.ArithmeticModel.valuation p ↑m) fun m =>
                              Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} B
                                (Sigma.mk.{u_1, 0} c m))))
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (32 : Real) (Real.log U))
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys (Real.log U))
                              (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B)))
                          (HDiv.hDiv.{0, 0, 0} Aval ↑p)) := by sorry

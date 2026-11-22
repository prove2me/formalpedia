-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:10:30.488974+00:00
-- url     : https://prove2.me/theorems/c1963e83-8310-4fe3-84ef-5e52aa64bbba
-- title:
--   Within-cell covariance and mean agreement control the tilted bridge covariance
-- statement:
--   Let $B$ have a nonempty head set and let $\xi$ be a bridge parameter. Let $F,G$ be real statistics on its sample space. Suppose under every actual tilted cell law the absolute covariance of $F,G$ is at most $e_{\rm cov}$, the expectations of $F$ in any two cells differ by at most $e_{\rm mean}\ge0$, and $|G|\le K$ pointwise with $K\ge0$. Then under the globally tilted bridge law,
--   $$|\operatorname{Cov}_{\xi}(F,G)|\le e_{\rm cov}+2K e_{\rm mean}.$$
--   Thus replacing a global covariance by component covariances has an explicit, controlled between-cell correction.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperNuisancePrimeLogRows.lean#L269-L398

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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (F G :
    Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) →
      Real)
  {covError meanError K : Real},
  LE.le.{0} (0 : Real) meanError →
    LE.le.{0} (0 : Real) K →
      (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
          LE.le.{0}
            (abs.{0}
              (Erdos390.Full.FiniteProbability.covariance.{0}
                (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c)
                  (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c))
                (fun x => F (Sigma.mk.{u_1, 0} c x)) fun x => G (Sigma.mk.{u_1, 0} c x)))
            covError) →
        (∀ (c c' : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.FiniteProbability.expect.{0}
                    (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c)
                      (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c))
                    fun x => F (Sigma.mk.{u_1, 0} c x))
                  (Erdos390.Full.FiniteProbability.expect.{0}
                    (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{u_1, u_2} B c')
                      (Erdos390.Full.FiniteProbability.sigmaCellScore.{u_1, 0}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.scaledBridgeScore.{u_1, u_2} B xi) c'))
                    fun x => F (Sigma.mk.{u_1, 0} c' x))))
              meanError) →
          (∀
              (m :
                Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
              LE.le.{0} (abs.{0} (G m)) K) →
            LE.le.{0}
              (abs.{0}
                (Erdos390.Full.FiniteProbability.covariance.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi) F G))
              (HAdd.hAdd.{0, 0, 0} covError (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) K) meanError)) := by sorry

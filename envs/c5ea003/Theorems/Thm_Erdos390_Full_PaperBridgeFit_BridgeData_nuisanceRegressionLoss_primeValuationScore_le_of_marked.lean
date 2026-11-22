-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_nuisanceRegressionLoss_primeValuationScore_le_of_marked
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceRegressionLoss_primeValuationScore_le_of_marked
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:17:58.308224+00:00
-- url     : https://prove2.me/theorems/76537164-9952-4e75-a28d-f87670feccb6
-- title:
--   Marked nuisance bounds control regression loss
-- statement:
--   Let $B$ be bridge data with nonempty head set, $\xi$ a tilt parameter, and $\gamma>0$. Suppose its nuisance covariance operator $T$ satisfies $\langle z,Tz\rangle\ge\gamma\|z\|^2$. Suppose the band reciprocal-prime mass is at most $H$, and every nuisance coordinate statistic has covariance of absolute value at most $C/p$ with each prime valuation, where $C\ge0$. Let $b_c$ be the nuisance covariance vector of the score $\sum_pc_pv_p$ and $a_c$ its regression coefficient. If $d$ is the number of nuisance coordinates,
--
--   $$\langle a_c,b_c\rangle\le\frac{dC^2H}{\gamma}\sum_p\frac{c_p^2}{p}.$$
--
--   This places nuisance regression loss in the same reciprocal-prime square norm as the principal score.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalActualBandQuadraticTransfer.lean#L817-L936

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceRegressionLoss_primeValuationScore_le_of_marked :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B) {gamma Cmarked totalWeight : Real}
  (hgamma : LT.lt.{0} (0 : Real) gamma),
  LE.le.{0} (0 : Real) Cmarked →
    ∀
      (hgap :
        ∀ (z : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B),
          LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)))
            (Inner.inner.{0, u_1} Real z
              ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi :
                  Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B →
                    Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B)
                z))),
      LE.le.{0}
          (∑ p :
            Erdos390.Full.ArithmeticBandGeometry.BandPrime
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
            Erdos390.Full.PaperSquarefreeSlowQuadraticLower.reciprocalWeight p)
          totalWeight →
        (∀
            (z :
              Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))
            (p :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
            LE.le.{0}
              (abs.{0}
                (Erdos390.Full.FiniteProbability.covariance.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                  (fun
                      (m :
                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                    WithLp.ofLp.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2} B m) z)
                  fun
                    (m :
                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                  Erdos390.Full.ArithmeticModel.valuation (↑p : Nat)
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m)))
              (HMul.hMul.{0, 0, 0} Cmarked (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(↑p : Nat) : Real)))) →
          ∀
            (c :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                Real),
            LE.le.{0}
              (Inner.inner.{0, u_1} Real
                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCoefficientOfScore.{u_1, u_2} B xi hgamma hgap
                  (Erdos390.Full.PaperBridgeFit.BridgeData.primeValuationScore.{u_1, u_2} B c))
                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceVector.{u_1, u_2} B xi
                  (Erdos390.Full.PaperBridgeFit.BridgeData.primeValuationScore.{u_1, u_2} B c)))
              (HMul.hMul.{0, 0, 0}
                (HDiv.hDiv.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0}
                      (↑(Fintype.card.{u_1}
                            (Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))) :
                        Real)
                      (HPow.hPow.{0, 0, 0} Cmarked (2 : Nat)))
                    totalWeight)
                  gamma)
                (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeCoefficientL2Sq c)) := by sorry

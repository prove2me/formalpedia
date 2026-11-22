-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualSquarefreeMarkedRow_sub_reference_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeMarkedRow_sub_reference_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:11:45.074716+00:00
-- url     : https://prove2.me/theorems/fe74bb35-db2b-41cb-b52e-f10f497146bf
-- title:
--   Compensated marked-row transfer from signed covariance entries
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $B$ be a bridge with finite head and band sets, and write $t_p=\log p/\log y_n$, $h_i$ for harmonic band masses, $\alpha_i$ for band centers, and $j(p)$ for the band of $p$. Let $R_{pr}$ be its squarefree Poisson–Dickman reference entry, $I_p=\mathbf1_{p\mid m}$, and $\mu_\xi$ its tilted law. Assume the head set is nonempty and, for every band prime pair, $|\operatorname{Cov}_{\mu_\xi}(I_p,I_r)-R_{pr}|\le e_o/(pr)+\mathbf1_{p=r}(e_d/p+e_2/p^2)$, where $e_o\ge0$. For a raw band-gauge vector $q$, write $a_r$ for its actual compensated prime coefficients and $Q_q$ for its post-band squarefree score. If $\sum_r|a_r|/r\le C_1w$, then for every band prime $p$,
--
--   $$\left|\operatorname{Cov}_{\mu_\xi}(I_p,Q_q)-\sum_r a_rR_{pr}\right|\le\frac{e_oC_1w}{p}+|a_p|\left(\frac{e_d}{p}+\frac{e_2}{p^2}\right).$$
--
--   The transfer keeps the two diagonal reciprocal orders separate from the off-diagonal coefficient sum.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualSquarefreeMarkedRow.lean#L51-L163

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeMarkedRow_sub_reference_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
  {epsilonOff epsilonDiag epsilonSecond CL1 w : Real},
  LE.le.{0} (0 : Real) epsilonOff →
    LE.le.{0}
        (∑
          r ∈
            Erdos390.Full.ArithmeticModel.primeBand
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
          HMul.hMul.{0, 0, 0}
            (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q r))
            (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑r))
        (HMul.hMul.{0, 0, 0} CL1 w) →
      (∀ (p r : Nat),
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              p →
            Membership.mem.{0, 0}
                (Erdos390.Full.ArithmeticModel.primeBand
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                r →
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) p r)
                    (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      p r)))
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                    (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑r))
                  (ite.{1} (Eq.{1} p r)
                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonDiag (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                      (HMul.hMul.{0, 0, 0} epsilonSecond
                        (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat))))
                    (0 : Real)))) →
        ∀ {p : Nat},
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              p →
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.FiniteProbability.covariance.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                    (fun m =>
                      Erdos390.Full.ArithmeticModel.divInd p
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m))
                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1, u_2} B q))
                  (∑
                    r ∈
                      Erdos390.Full.ArithmeticModel.primeBand
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                    HMul.hMul.{0, 0, 0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q r)
                      (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        p r))))
              (HAdd.hAdd.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff CL1) w)
                  (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                (HMul.hMul.{0, 0, 0}
                  (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q p))
                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonDiag (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                    (HMul.hMul.{0, 0, 0} epsilonSecond
                      (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))))) := by sorry

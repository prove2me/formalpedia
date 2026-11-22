-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_referenceMarkedRow_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.referenceMarkedRow_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:18:25.095472+00:00
-- url     : https://prove2.me/theorems/5d59ec6e-17aa-4a63-a31b-00377ef8a194
-- title:
--   Reference marked-row estimate from coefficient ledgers
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $B$ be a bridge with finite head and band sets, and write $t_p=\log p/\log y_n$, $h_i$ for harmonic band masses, $\alpha_i$ for band centers, and $j(p)$ for the band of $p$. Let $R_{pr}$ be its squarefree Poisson–Dickman reference entry, $I_p=\mathbf1_{p\mid m}$, and $\mu_\xi$ its tilted law. For a raw band-gauge vector $q$, let $a_r$ be its actual compensated prime coefficients. Suppose $C_F,C_K\ge0$, $|a_r|\le C_{\sup}w$, $\sum_r|a_r|/r\le C_1w$, $|F(t_r)|\le C_F$, and $|K(t_r,t_s)|\le C_K$ for all band primes, where $F$ and $K$ are the Dickman diagonal function and covariance kernel. Then
--
--   $$\left|\sum_r a_rR_{pr}\right|\le(C_KC_1+C_FC_{\sup})\frac w p\qquad(p\in\mathcal P_{n,W}).$$
--
--   The same coefficient ledgers that describe a compensated vector control its reference marked row.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualSquarefreeMarkedRow.lean#L165-L298

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.referenceMarkedRow_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) {CF CKernel Csup CL1 w : Real},
  LE.le.{0} (0 : Real) CF →
    LE.le.{0} (0 : Real) CKernel →
      (∀ (r : Nat),
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              r →
            LE.le.{0}
              (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q r))
              (HMul.hMul.{0, 0, 0} Csup w)) →
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
          (∀
              (r :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0}
                (abs.{0}
                  (Erdos390.Full.DickmanBasic.F
                    (Erdos390.Full.ArithmeticModel.tPrime
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      ↑r)))
                CF) →
            (∀
                (r s :
                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                LE.le.{0}
                  (abs.{0}
                    (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                      (Erdos390.Full.ArithmeticModel.tPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        ↑r)
                      (Erdos390.Full.ArithmeticModel.tPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        ↑s)))
                  CKernel) →
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
                            p r)))
                    (HMul.hMul.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} CKernel CL1) (HMul.hMul.{0, 0, 0} CF Csup)) w)
                      (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p)) := by sorry

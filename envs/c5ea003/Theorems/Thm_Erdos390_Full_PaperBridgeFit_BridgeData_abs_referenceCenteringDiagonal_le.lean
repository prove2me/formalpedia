-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_referenceCenteringDiagonal_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringDiagonal_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:11:13.963123+00:00
-- url     : https://prove2.me/theorems/67ddb51f-9f28-4930-a136-8e3c891c2894
-- title:
--   Diagonal centering error in the sharp reference row
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $B$ be a bridge with finite head and band sets, and write $t_p=\log p/\log y_n$, $h_i$ for harmonic band masses, $\alpha_i$ for band centers, and $j(p)$ for the band of $p$. Let $R_{pr}$ be its squarefree Poisson–Dickman reference entry, $I_p=\mathbf1_{p\mid m}$, and $\mu_\xi$ its tilted law. Write $d_p=\alpha_{j(p)}-t_p$ for the prime deviation. Let $w,C_F,R\ge0$. Assume $|F(t_p)-F(\alpha_{j(p)})|\le C_F|d_p|$ and $|d_p|\le w$ for every band prime, and $|x_j|\le R$ for every band. Then
--
--   $$|E_i^{\rm diag}(x)|\le2C_FwR\qquad\text{for every }i,$$
--
--   where $E^{\rm diag}$ is the source diagonal centering error.
--
--   Exact fiber centering gives a relative estimate without dividing the final bound by the smallest band center.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperReferenceSharpPrimeGraph.lean#L628-L753

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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringDiagonal_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {w CF R : Real},
  LE.le.{0} (0 : Real) w →
    LE.le.{0} (0 : Real) CF →
      LE.le.{0} (0 : Real) R →
        (∀
            (p :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.DickmanBasic.F
                    (Erdos390.Full.ArithmeticModel.tPrime
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      ↑p))
                  (Erdos390.Full.DickmanBasic.F
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B
                      (Erdos390.Full.ArithmeticBandGeometry.Partition.band.{u_2}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) p)))))
              (HMul.hMul.{0, 0, 0} CF
                (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)))) →
          (∀
              (p :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)) w) →
            ∀ (x : Band → Real),
              (∀ (j : Band), LE.le.{0} (abs.{0} (x j)) R) →
                ∀ (i : Band),
                  LE.le.{0}
                    (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringDiagonal.{u_1, u_2} B x i))
                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) CF) w) R) := by sorry

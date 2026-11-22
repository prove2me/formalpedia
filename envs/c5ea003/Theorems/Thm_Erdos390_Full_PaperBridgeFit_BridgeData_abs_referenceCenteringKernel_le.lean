-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_referenceCenteringKernel_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringKernel_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:12:39.197973+00:00
-- url     : https://prove2.me/theorems/3e7c2c08-3258-41a1-ac41-c8e600407236
-- title:
--   Kernel centering error from the global deviation ledger
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $B$ be a bridge with finite head and band sets, and write $t_p=\log p/\log y_n$, $h_i$ for harmonic band masses, $\alpha_i$ for band centers, and $j(p)$ for the band of $p$. Let $R_{pr}$ be its squarefree Poisson–Dickman reference entry, $I_p=\mathbf1_{p\mid m}$, and $\mu_\xi$ its tilted law. Write $d_p=\alpha_{j(p)}-t_p$ for the prime deviation. Let $C_K,R\ge0$ and $w\in\mathbb R$. Assume $|K(t_p,t_q)|\le C_Kt_p$ for all band primes and $\sum_p|d_p|/p\le7w$. If $|x_j|\le R$ for every band, then the source kernel centering error satisfies
--
--   $$|E_i^{\rm ker}(x)|\le7C_KwR\qquad\text{for every }i.$$
--
--   The global deviation ledger controls this centering error independently of the number of mesh bands.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperReferenceSharpPrimeGraph.lean#L755-L861

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
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringKernel_le :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {w CKernel R : Real},
  LE.le.{0} (0 : Real) CKernel →
    LE.le.{0} (0 : Real) R →
      (∀
          (p q :
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
                  ↑p)
                (Erdos390.Full.ArithmeticModel.tPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  ↑q)))
            (HMul.hMul.{0, 0, 0} CKernel
              (Erdos390.Full.ArithmeticModel.tPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                ↑p))) →
        LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
            (HMul.hMul.{0, 0, 0} (7 : Real) w) →
          ∀ (x : Band → Real),
            (∀ (j : Band), LE.le.{0} (abs.{0} (x j)) R) →
              ∀ (i : Band),
                LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringKernel.{u_1, u_2} B x i))
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (7 : Real) CKernel) w) R) := by sorry

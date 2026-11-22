-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_main_norm_sq_le_fastSharp_add_storedSlow
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.main_norm_sq_le_fastSharp_add_storedSlow
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:18:05.561053+00:00
-- url     : https://prove2.me/theorems/d8e6b45c-aa4c-4705-992f-4256a70e20ba
-- title:
--   The main coordinate norm is controlled by fast and stored slow coordinates
-- statement:
--   Let $B$ be bridge data, $u$ a main-space vector, $q_f,q_r$ raw band-gauge vectors, and $\lambda\in\mathbb R$. Let $\|\cdot\|_\sharp$ be the paper sharp norm, $w$ the stored slow scale, and $S_B$ the source's sum of squared gauge centers. Assume $C_r\ge0$, $\|q_r\|_\sharp\le C_rw$, the raw gauge of $u$ is $q_f-\lambda q_r$, and $u_{\rm slow}=w\lambda$. Then
--   $$\|u\|^2\le[1+2S_B(1+C_r^2)]\bigl(\|q_f\|_\sharp^2+(w\lambda)^2\bigr).$$
--   This finite coordinate comparison converts fast/slow variance control into main-space coercivity.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperMainFastSlowCoordinates.lean#L114-L215

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.main_norm_sq_le_fastSharp_add_storedSlow :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  (u : Erdos390.Full.PaperBridgeFit.BridgeData.MainSpace.{u_1, u_2} B)
  (qFast qReg : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) (lambda Creg : Real),
  LE.le.{0} (0 : Real) Creg →
    LE.le.{0}
        (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
          (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
          (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
          (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
            (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
          qReg)
        (HMul.hMul.{0, 0, 0} Creg (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)) →
      Eq.{u_2 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.rawGaugeOfMain.{u_1, u_2} B u)
          (HSub.hSub.{u_2, u_2, u_2} qFast (HSMul.hSMul.{0, u_2, u_2} lambda qReg)) →
        Eq.{1} (WithLp.ofLp.{u_2} u Erdos390.Full.PaperBridgeFit.MainCoord.slow.{u_2})
            (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B) lambda) →
          LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_2} u) (2 : Nat))
            (HMul.hMul.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0} (1 : Real)
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (2 : Real)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.gaugeCenterSquareSum.{u_1, u_2} B))
                  (HAdd.hAdd.{0, 0, 0} (1 : Real) (HPow.hPow.{0, 0, 0} Creg (2 : Nat)))))
              (HAdd.hAdd.{0, 0, 0}
                (HPow.hPow.{0, 0, 0}
                  (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                      (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                    qFast)
                  (2 : Nat))
                (HPow.hPow.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B) lambda) (2 : Nat)))) := by sorry

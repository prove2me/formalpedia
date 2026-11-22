-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_slow_div_mul_actualTwoStageCompensatedVariance
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.slow_div_mul_actualTwoStageCompensatedVariance
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:18:46.276452+00:00
-- url     : https://prove2.me/theorems/9d913470-9d16-4155-9d97-ee55f9bf8a78
-- title:
--   The slow coordinate of a Schur solution obeys the compensated scalar equation
-- statement:
--   Let $B$ be bridge data with nonempty finite head and band index sets, $\xi$ a parameter, and $\gamma>0$ such that the nuisance covariance operator satisfies $\langle z,N_\xi z\rangle\ge\gamma\|z\|^2$. Let $e$ be a linear automorphism of the raw band gauge equal to the actual band Schur map. For a band target $\Delta$, suppose a main vector $u$ solves the exact Schur equation $S_\xi u=\operatorname{main}(\operatorname{normalizedTarget}(\Delta))$. Let $V_{\rm comp}$ be the variance of the actual two-stage compensated score and $T_{\rm comp}(\Delta)$ the corresponding compensated normalized target. Then
--   $$\frac{u_{\rm slow}}{w}\,V_{\rm comp}=T_{\rm comp}(\Delta).$$
--   The identity isolates the slow coefficient after eliminating nuisance and fast-band directions.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperExactTwoStageTargetSolve.lean#L622-L725

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.slow_div_mul_actualTwoStageCompensatedVariance :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  {gamma : Real} (hgamma : LT.lt.{0} (0 : Real) gamma)
  (hgap :
    ∀ (z : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B),
      LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)))
        (Inner.inner.{0, u_1} Real z
          ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi) z)))
  (e :
    LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
  (∀ (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
      Eq.{u_2 + 1} (e q)
        ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2} B xi hgamma hgap) q)) →
    ∀ (Delta : Band → Real) (u : Erdos390.Full.PaperBridgeFit.BridgeData.MainSpace.{u_1, u_2} B),
      Eq.{u_2 + 1}
          ((Erdos390.Full.PaperBridgeFit.BridgeData.exactSchurCovarianceOperator.{u_1, u_2} B xi hgamma hgap) u)
          (Erdos390.Full.PaperBridgeFit.BridgeData.mainPart.{u_1, u_2} B
            (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedTarget.{u_1, u_2} B Delta)) →
        Eq.{1}
          (HMul.hMul.{0, 0, 0}
            (HDiv.hDiv.{0, 0, 0} (WithLp.ofLp.{u_2} u Erdos390.Full.PaperBridgeFit.MainCoord.slow.{u_2})
              (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B))
            (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1, u_2} B xi hgamma hgap e))
          (Erdos390.Full.PaperBridgeFit.BridgeData.compensatedNormalizedTarget.{u_1, u_2} B xi hgamma hgap e Delta) := by sorry

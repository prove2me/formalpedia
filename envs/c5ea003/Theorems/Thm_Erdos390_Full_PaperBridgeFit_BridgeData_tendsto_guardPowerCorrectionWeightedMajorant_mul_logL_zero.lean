-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:19:10.261675+00:00
-- url     : https://prove2.me/theorems/3a7a63a1-689e-4883-b359-e69c825228bd
-- title:
--   Weighted guard power correction survives a harmonic loss
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, and $\mathcal P=\{p\text{ prime}:W<p\le Y\}$. Write $E_g(K,d)=(K^2+K)(7d+2d^2)$, the guard power-correction row error. Fix natural ledger constants $C_{\rm prom},C_{\rm bank}$ and $C_e,D\ge0$. Let $r_n$ be their census ratio majorant and $G_n=Y E_g(C_eL,Dr_n)$ the weighted guard power-correction majorant. Then
--
--   $$G_n\log L\longrightarrow0.$$
--
--   The guard loss is smaller than the moving-low center scale, which is comparable to the reciprocal of $\log L$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgeCanonicalGuardPowerCorrection.lean#L815-L926

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero :
∀ (Cprom Cbank : Nat) {Cenv D : Real},
  LE.le.{0} (0 : Real) Cenv →
    LE.le.{0} (0 : Real) D →
      Filter.Tendsto.{0, 0}
        (fun n =>
          HMul.hMul.{0, 0, 0}
            (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n)
            (Real.log (Erdos390.Full.Scale.L n)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) := by sorry

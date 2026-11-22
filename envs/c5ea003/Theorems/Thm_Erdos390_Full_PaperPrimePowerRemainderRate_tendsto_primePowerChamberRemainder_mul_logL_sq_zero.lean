-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerChamberRemainder_mul_logL_sq_zero
-- name    : Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerChamberRemainder_mul_logL_sq_zero
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:22:39.441303+00:00
-- url     : https://prove2.me/theorems/2d3b33d1-2c9c-4595-97cd-8cd44f45e908
-- title:
--   The chamber remainder preserves two logarithmic decay rates
-- statement:
--   Write $L_n=\log n$, $a=1/\rho(U)$ for the fixed Dickman constant, $k_n=(2B/L_n)\exp(2B/\log W)$, $P_n=2[G_0(2k_n+k_n^2)+\epsilon_n+aG_0(2k_n+k_n^2)]$, and $R_n=2[P_n(1+2a)+P_n^2]+P_n$. Thus $R_n$ is the source's common prime-power chamber remainder. For arbitrary real $G_0,B$, natural $W$, and real sequence $\epsilon_n$, assume $\epsilon_n\to0$ and $\epsilon_n(\log L_n)^2\to0$. Then
--   $$R_n(\log L_n)^2\longrightarrow0.$$
--   This supplies the additional decay needed before summing over a harmonic prime row.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerRemainderRate.lean#L242-L350

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

theorem Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerChamberRemainder_mul_logL_sq_zero :
∀ (epsilon : Nat → Real) (G₀ B : Real) (W : Nat),
  Filter.Tendsto.{0, 0} epsilon Filter.atTop.{0} (nhds.{0} (0 : Real)) →
    Filter.Tendsto.{0, 0}
        (fun n => HMul.hMul.{0, 0, 0} (epsilon n) (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.Scale.L n)) (2 : Nat)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) →
      Filter.Tendsto.{0, 0}
        (fun n =>
          HMul.hMul.{0, 0, 0}
            (Erdos390.Full.PaperPrimePowerFourDisplays.primePowerChamberRemainder (epsilon n) G₀
              (Erdos390.Full.PaperPrimePowerChamberError.coefficientScale B W n))
            (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.Scale.L n)) (2 : Nat)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) := by sorry

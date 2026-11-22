-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerChamberRemainder_zero_and_rate
-- name    : Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerChamberRemainder_zero_and_rate
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:23:09.258889+00:00
-- url     : https://prove2.me/theorems/504548f3-dcf8-4d79-84a1-4e0a99bc989c
-- title:
--   The chamber remainder preserves one logarithmic decay rate
-- statement:
--   Write $L_n=\log n$, $a=1/\rho(U)$ for the fixed Dickman constant, $k_n=(2B/L_n)\exp(2B/\log W)$, $P_n=2[G_0(2k_n+k_n^2)+\epsilon_n+aG_0(2k_n+k_n^2)]$, and $R_n=2[P_n(1+2a)+P_n^2]+P_n$. Thus $R_n$ is the source's common prime-power chamber remainder. For any real sequence $\epsilon_n$, real constants $G_0,B$, and natural number $W$, if $\epsilon_n\to0$ and $\epsilon_n\log L_n\to0$, then
--   $$R_n\longrightarrow0,\qquad R_n\log L_n\longrightarrow0.$$
--   This propagates the marked-profile error through local restoration and covariance formation. No sign assumptions on these parameters are needed for this limit statement.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerRemainderRate.lean#L99-L240

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

theorem Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerChamberRemainder_zero_and_rate :
∀ (epsilon : Nat → Real) (G₀ B : Real) (W : Nat),
  Filter.Tendsto.{0, 0} epsilon Filter.atTop.{0} (nhds.{0} (0 : Real)) →
    Filter.Tendsto.{0, 0} (fun n => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) →
      And
        (Filter.Tendsto.{0, 0}
          (fun n =>
            Erdos390.Full.PaperPrimePowerFourDisplays.primePowerChamberRemainder (epsilon n) G₀
              (Erdos390.Full.PaperPrimePowerChamberError.coefficientScale B W n))
          Filter.atTop.{0} (nhds.{0} (0 : Real)))
        (Filter.Tendsto.{0, 0}
          (fun n =>
            HMul.hMul.{0, 0, 0}
              (Erdos390.Full.PaperPrimePowerFourDisplays.primePowerChamberRemainder (epsilon n) G₀
                (Erdos390.Full.PaperPrimePowerChamberError.coefficientScale B W n))
              (Real.log (Erdos390.Full.Scale.L n)))
          Filter.atTop.{0} (nhds.{0} (0 : Real))) := by sorry

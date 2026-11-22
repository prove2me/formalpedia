-- Prove2me | Theorems.Thm_Erdos390_Full_OmittedTiltHarmonicRate_tendsto_omittedTiltMajorant_mul_logL_sq_zero
-- name    : Erdos390.Full.OmittedTiltHarmonicRate.tendsto_omittedTiltMajorant_mul_logL_sq_zero
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:50:14.304918+00:00
-- url     : https://prove2.me/theorems/86229bdc-d936-4e5b-a407-081ff9b659cb
-- title:
--   Two harmonic losses in the omitted-tilt majorant
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix $B\ge0$, $C,c>0$ and an integer $W>1$. Define the omitted-tilt normalizer majorant by $$M_n=\exp\!\left(\frac B{L}\frac{\log\lfloor Cn\rfloor}{\log W}\right)\frac B{L}\frac2c\sum_{W<p\le Y\atop p\ {\rm prime}}\frac1p.$$
--
--   $$M_n(\log L)^2\longrightarrow0.$$
--
--   The second harmonic margin is needed when an aggregated row is divided by a scale comparable to the reciprocal of $\log L$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/OmittedTiltHarmonicRate.lean#L160-L282

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.OmittedTiltHarmonicRate.tendsto_omittedTiltMajorant_mul_logL_sq_zero :
∀ (B C c : Real) (W : Nat),
  LE.le.{0} (0 : Real) B →
    LT.lt.{0} (0 : Real) C →
      LT.lt.{0} (0 : Real) c →
        LT.lt.{0} (1 : Nat) W →
          Filter.Tendsto.{0, 0}
            (fun n =>
              HMul.hMul.{0, 0, 0} (Erdos390.Full.OmittedTiltMarkedProbability.omittedTiltMajorant B C c W n)
                (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.Scale.L n)) (2 : Nat)))
            Filter.atTop.{0} (nhds.{0} (0 : Real)) := by sorry

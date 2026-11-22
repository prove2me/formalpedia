-- Prove2me | Theorems.Thm_Erdos390_Full_OmittedTiltHarmonicRate_tendsto_omittedTiltMajorant_mul_logL_zero
-- name    : Erdos390.Full.OmittedTiltHarmonicRate.tendsto_omittedTiltMajorant_mul_logL_zero
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:02:34.326913+00:00
-- url     : https://prove2.me/theorems/0d1c7aa2-1588-41bf-975b-091a9d3cdef4
-- title:
--   One harmonic loss in the omitted-tilt majorant
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix $B\ge0$, $C,c>0$ and an integer $W>1$. Define the omitted-tilt normalizer majorant by $$M_n=\exp\!\left(\frac B{L}\frac{\log\lfloor Cn\rfloor}{\log W}\right)\frac B{L}\frac2c\sum_{W<p\le Y\atop p\ {\rm prime}}\frac1p.$$
--
--   $$M_n\log L\longrightarrow0.$$
--
--   The normalizer error remains negligible after one complete harmonic-band summation.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/OmittedTiltHarmonicRate.lean#L29-L158

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.OmittedTiltHarmonicRate.tendsto_omittedTiltMajorant_mul_logL_zero :
∀ (B C c : Real) (W : Nat),
  LE.le.{0} (0 : Real) B →
    LT.lt.{0} (0 : Real) C →
      LT.lt.{0} (0 : Real) c →
        LT.lt.{0} (1 : Nat) W →
          Filter.Tendsto.{0, 0}
            (fun n =>
              HMul.hMul.{0, 0, 0} (Erdos390.Full.OmittedTiltMarkedProbability.omittedTiltMajorant B C c W n)
                (Real.log (Erdos390.Full.Scale.L n)))
            Filter.atTop.{0} (nhds.{0} (0 : Real)) := by sorry

-- Prove2me | Theorems.Thm_Erdos390_Full_OmittedTiltMarkedProbability_tendsto_omittedTiltMajorant_zero
-- name    : Erdos390.Full.OmittedTiltMarkedProbability.tendsto_omittedTiltMajorant_zero
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:02:56.848629+00:00
-- url     : https://prove2.me/theorems/d8ed4171-d260-45f5-8ab3-59f079a1f615
-- title:
--   Vanishing of the omitted-tilt normalizer majorant
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix $B\ge0$, $C,c>0$ and an integer $W>1$. Define the omitted-tilt normalizer majorant by $$M_n=\exp\!\left(\frac B{L}\frac{\log\lfloor Cn\rfloor}{\log W}\right)\frac B{L}\frac2c\sum_{W<p\le Y\atop p\ {\rm prime}}\frac1p.$$
--
--   $$M_n\longrightarrow0\quad(n\to\infty).$$
--
--   The explicit normalizer perturbation is uniformly negligible over the omitted prime subsets.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/OmittedTiltMarkedProbability.lean#L47-L153

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.OmittedTiltMarkedProbability.tendsto_omittedTiltMajorant_zero :
∀ (B C c : Real) (W : Nat),
  LE.le.{0} (0 : Real) B →
    LT.lt.{0} (0 : Real) C →
      LT.lt.{0} (0 : Real) c →
        LT.lt.{0} (1 : Nat) W →
          Filter.Tendsto.{0, 0} (Erdos390.Full.OmittedTiltMarkedProbability.omittedTiltMajorant B C c W)
            Filter.atTop.{0} (nhds.{0} (0 : Real)) := by sorry

-- Prove2me | Theorems.Thm_Erdos390_Full_PaperTiltSmallness_eventually_actual_valuationTilt_small
-- name    : Erdos390.Full.PaperTiltSmallness.eventually_actual_valuationTilt_small
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:24:09.86335+00:00
-- url     : https://prove2.me/theorems/590930df-89c7-4a44-9916-400429115d23
-- title:
--   Eventual smallness of the actual valuation-tilt majorant
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix $B\ge0$, $C,c>0$ and an integer $W>1$. Define the omitted-tilt normalizer majorant by $$M_n=\exp\!\left(\frac B{L}\frac{\log\lfloor Cn\rfloor}{\log W}\right)\frac B{L}\frac2c\sum_{W<p\le Y\atop p\ {\rm prime}}\frac1p.$$
--
--   $$M_n<1\qquad\text{for all sufficiently large }n.$$
--
--   The denominator perturbation is controlled after fixing the cutoff and coefficient box, before taking the physical scale large.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperTiltSmallness.lean#L22-L136

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.PaperTiltSmallness.eventually_actual_valuationTilt_small :
∀ (B C c : Real) (W : Nat),
  LE.le.{0} (0 : Real) B →
    LT.lt.{0} (0 : Real) C →
      LT.lt.{0} (0 : Real) c →
        LT.lt.{0} (1 : Nat) W →
          ∀ᶠ (n : Nat) in Filter.atTop.{0},
            LT.lt.{0}
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0}
                  (Real.exp
                    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} B (Erdos390.Full.Scale.L n))
                      (HDiv.hDiv.{0, 0, 0} (Real.log ↑(Erdos390.Full.ArithmeticModel.physicalBound C n))
                        (Real.log ↑W))))
                  (HDiv.hDiv.{0, 0, 0} B (Erdos390.Full.Scale.L n)))
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (2 : Real) c)
                  (Erdos390.Full.PrimeSums.bandReciprocalSum n W)))
              (1 : Real) := by sorry

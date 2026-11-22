-- Prove2me | Theorems.Thm_Erdos390_Full_FriableAsymptotic_dickmanWeight_pnt_bound
-- name    : Erdos390.Full.FriableAsymptotic.dickmanWeight_pnt_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:45:15.753542+00:00
-- url     : https://prove2.me/theorems/06ddf491-5ed7-42cf-8ba1-8b8c103dcf01
-- title:
--   PNT error for the Dickman Abel weight
-- statement:
--   Let $X\ge1$, $C\ge0$, and $X_0\le z<y$ with $z\ge2$ be integers except for $C$. Suppose $|\theta(T)-T|\le CT/(\log T)^3$ for every integer $T\ge X_0$, where $\theta$ is the prime logarithmic sum, and $1\le\log X/\log t\le6$ throughout $[z,y]$. Set $f(m)=X\rho(\log X/\log m-1)/(m\log m)$. Let $A_f=f(y)y-f(z+1)z-\sum_{z<m<y}(f(m+1)-f(m))m$ be the discrete Abel main term.
--
--   $$\left|\sum_{z<p\le y\atop p\ {\rm prime}}f(p)\log p-A_f\right|\le\frac{500CX}{\log z}.$$
--
--   This supplies the quantitative prime-sum replacement in the friable-number recurrence.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FriableAsymptotic.lean#L1355-L1579

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.FriableAsymptotic.dickmanWeight_pnt_bound :
∀ (X : Nat),
  LE.le.{0} (1 : Nat) X →
    ∀ {C : Real},
      LE.le.{0} (0 : Real) C →
        ∀ {X₀ z y : Nat},
          (∀ (T : Nat),
              LE.le.{0} X₀ T →
                LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (Erdos390.Full.FriableAsymptotic.primeLogSumUpTo T) ↑T))
                  (HMul.hMul.{0, 0, 0} C (HDiv.hDiv.{0, 0, 0} (↑T) (HPow.hPow.{0, 0, 0} (Real.log ↑T) (3 : Real))))) →
            LE.le.{0} X₀ z →
              LE.le.{0} (2 : Nat) z →
                LT.lt.{0} z y →
                  (∀ (t : Real),
                      Membership.mem.{0, 0} (Set.Icc.{0} ↑z ↑y) t →
                        And (LE.le.{0} (1 : Real) (Erdos390.Full.FriableAsymptotic.logRatio (↑X) t))
                          (LE.le.{0} (Erdos390.Full.FriableAsymptotic.logRatio (↑X) t) (6 : Real))) →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FriableAsymptotic.primeThetaWeightedInterval
                            (Erdos390.Full.FriableAsymptotic.dickmanThetaWeight X) z y)
                          (Erdos390.Full.FriableAsymptotic.integerAbelMain
                            (Erdos390.Full.FriableAsymptotic.dickmanThetaWeight X) z y)))
                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (500 : Real) C) ↑X) (Real.log ↑z)) := by sorry

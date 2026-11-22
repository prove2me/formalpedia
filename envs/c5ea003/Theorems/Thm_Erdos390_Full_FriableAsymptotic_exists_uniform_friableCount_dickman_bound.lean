-- Prove2me | Theorems.Thm_Erdos390_Full_FriableAsymptotic_exists_uniform_friableCount_dickman_bound
-- name    : Erdos390.Full.FriableAsymptotic.exists_uniform_friableCount_dickman_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:50:04.313797+00:00
-- url     : https://prove2.me/theorems/aeb1565d-6b9e-4040-9b65-deae85cf4c34
-- title:
--   Uniform Dickman estimate through the four-mark range
-- statement:
--   Let $\Psi(X,y)$ count positive integers at most $X$ whose prime factors are at most $y$. There exist $K>0$ and an integer $Y_0$ such that, for all integers $Y_0\le y\le X$ satisfying $\log X\le5\log y$,
--
--   $$\left|\Psi(X,y)-X\rho\!\left(\frac{\log X}{\log y}\right)\right|\le\frac{KX}{\log y}.$$
--
--   The estimate is uniform in the divisor range needed for up to four logarithmic marks.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FriableAsymptotic.lean#L2605-L2820

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.FriableAsymptotic.exists_uniform_friableCount_dickman_bound :
∃ K,
  And (LT.lt.{0} (0 : Real) K)
    (∃ Y₀,
      ∀ {X y : Nat},
        LE.le.{0} Y₀ y →
          LE.le.{0} y X →
            LE.le.{0} (Real.log ↑X) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑y)) →
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0} (↑(Erdos390.Full.FriableAsymptotic.friableCount X y))
                    (HMul.hMul.{0, 0, 0} (↑X)
                      (Erdos390.Full.DickmanBasic.rho (Erdos390.Full.FriableAsymptotic.dickmanU X y)))))
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} K ↑X) (Real.log ↑y))) := by sorry

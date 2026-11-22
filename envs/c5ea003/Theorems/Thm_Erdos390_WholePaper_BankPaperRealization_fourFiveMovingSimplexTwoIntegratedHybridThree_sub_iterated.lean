-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_fourFiveMovingSimplexTwoIntegratedHybridThree_sub_iterated
-- name    : Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexTwoIntegratedHybridThree_sub_iterated
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:56:15.046297+00:00
-- url     : https://prove2.me/theorems/ae0e4cd9-9ec7-4654-a47e-fe17b6684d7e
-- title:
--   Last-coordinate defect of the three-dimensional hybrid
-- statement:
--   Let $A,Y,y\in\mathbb N$ satisfy $2\le y\le A$, and let $u\in\mathbb R$. Let $H_3$ be the source hybrid with two coordinates integrated and the third evaluated at right endpoints using log-log cell masses. Let $I_3$ be the fully iterated cell product, $d$ the log-log density, $\lambda_y(x)$ the real logarithmic coordinate, and $D(c)$ the moving-face Lebesgue cell-defect sum with parameters $A,Y,y,u$. Then
--
--   $$H_3-I_3=\sum_{p=A+1}^{Y}\int_{p-1}^p d(x)\sum_{q=A+1}^{Y}\int_{q-1}^{q}d(z)D(\lambda_y(x)+\lambda_y(z))\,dz\,dx.$$
--
--   This exact formula isolates the error introduced by discretizing only the final coordinate.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveMovingSimplexCellIdentification.lean#L1608-L1808

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexTwoIntegratedHybridThree_sub_iterated :
∀ {A Y y : Nat} {u : Real},
  LE.le.{0} (2 : Nat) y →
    LE.le.{0} y A →
      Eq.{1}
        (HSub.hSub.{0, 0, 0}
          (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexTwoIntegratedHybridThree A Y y u)
          (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexIteratedRealCellProductThree A Y y u))
        (∑ p ∈ Finset.Ioc.{0} A Y,
          ∫ (x : Real) in ↑(HSub.hSub.{0, 0, 0} p (1 : Nat))..↑p,
            HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.BankPaperRealization.fourFiveLogLogLebesgueDensity x)
              (∑ q ∈ Finset.Ioc.{0} A Y,
                ∫ (z : Real) in ↑(HSub.hSub.{0, 0, 0} q (1 : Nat))..↑q,
                  HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.BankPaperRealization.fourFiveLogLogLebesgueDensity z)
                    (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                      (HAdd.hAdd.{0, 0, 0} (Erdos390.WholePaper.BankPaperRealization.fourFiveRealLogCoordinate y x)
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveRealLogCoordinate y z))))) := by sorry

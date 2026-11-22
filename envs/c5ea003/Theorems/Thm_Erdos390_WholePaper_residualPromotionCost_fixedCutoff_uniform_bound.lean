-- Prove2me | Theorems.Thm_Erdos390_WholePaper_residualPromotionCost_fixedCutoff_uniform_bound
-- name    : Erdos390.WholePaper.residualPromotionCost_fixedCutoff_uniform_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:24:44.250504+00:00
-- url     : https://prove2.me/theorems/3d2d0d7a-68ab-4a51-a94a-6d7b6a7c1516
-- title:
--   Uniform fixed-cutoff bound for residual promotion cost
-- statement:
--   There exists an absolute $K>0$ such that for every fixed natural $q\ge2$, all sufficiently large $n$ satisfy
--   $$\operatorname{PromotionCost}(n,\lfloor n/q\rfloor)\le K\frac{1+\log q}{q}\frac n{\log n}.$$
--   The constant $K$ is independent of $q$, while the eventual threshold may depend on $q$. This allows the promotion cost to be made small by choosing a large fixed cutoff parameter.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/CentralPromotionCostAsymptotic.lean#L230-L423

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

theorem Erdos390.WholePaper.residualPromotionCost_fixedCutoff_uniform_bound :
∃ K,
  And (LT.lt.{0} (0 : Real) K)
    (∀ (q : Nat),
      LE.le.{0} (2 : Nat) q →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          LE.le.{0} (↑(Erdos390.WholePaper.residualPromotionCost n (HDiv.hDiv.{0, 0, 0} n q)))
            (HMul.hMul.{0, 0, 0}
              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} K (HAdd.hAdd.{0, 0, 0} (1 : Real) (Real.log ↑q))) ↑q)
              (Erdos390.WholePaper.secondOrderScale n))) := by sorry

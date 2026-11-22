-- Prove2me | Theorems.Thm_Erdos390_WholePaper_eventually_paperExceptionalChargeEpsilon_le_power
-- name    : Erdos390.WholePaper.eventually_paperExceptionalChargeEpsilon_le_power
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:06:02.62403+00:00
-- url     : https://prove2.me/theorems/2d40eca7-d688-4d7a-a92b-16bc0e956a05
-- title:
--   Power bound for the exceptional charge error
-- statement:
--   For every real $\delta\ge0$, let $\varepsilon_\delta(n)$ be the canonical exceptional charge error and $C_R$ the paper exceptional Selberg remainder constant. Eventually in natural $n$,
--   $$\varepsilon_\delta(n)\le200C_R n^{\delta+8/9-1}.$$
--
--   The explicit power estimate makes the charge error usable in asymptotic budgets.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFixedExceptionalChargeAsymptotic.lean#L154-L247

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008

theorem Erdos390.WholePaper.eventually_paperExceptionalChargeEpsilon_le_power :
∀ {deltaStar : Real},
  LE.le.{0} (0 : Real) deltaStar →
    ∀ᶠ (n : Nat) in Filter.atTop.{0},
      LE.le.{0} (Erdos390.WholePaper.paperExceptionalChargeEpsilon deltaStar n)
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (200 : Real) Erdos390.WholePaper.paperExceptionalSelbergRemainderConstant)
          (HPow.hPow.{0, 0, 0} (↑n) (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} deltaStar (8 / 9 : Real)) (1 : Real)))) := by sorry

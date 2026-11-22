-- Prove2me | Theorems.Thm_Erdos390_WholePaper_eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
-- name    : Erdos390.WholePaper.eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:06:48.065582+00:00
-- url     : https://prove2.me/theorems/ea9eca1a-bf51-487f-b6d1-f383cd3828f4
-- title:
--   The normalized exceptional sieve remainder is negligible
-- statement:
--   Let $0\le\delta<1/18$ and suppose the head gap $g=d_W(2-r_0)$ is positive. Write $E(X_0,y,u)$ for the canonical exceptional remainder and $X_0(n)$ for the exceptional cutoff at exponent $\delta$. Eventually in natural $n$, uniformly for every natural $u>0$,
--   $$\frac un E(X_0(n),y(n),u)\le\frac g{16}.$$
--
--   This provides the remainder component of the clean-list loss budget.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentPaperCleanListAbsorption.lean#L455-L556

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008

theorem Erdos390.WholePaper.eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap :
∀ {W : Nat} {r0 deltaStar : Real},
  LE.le.{0} (0 : Real) deltaStar →
    LT.lt.{0} deltaStar (1 / 18 : Real) →
      LT.lt.{0} (0 : Real) (Erdos390.WholePaper.tangentPaperHeadGap W r0) →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (u : Nat),
            LT.lt.{0} (0 : Nat) u →
              LE.le.{0}
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} ↑u ↑n)
                  (Erdos390.WholePaper.tangentCanonicalExceptionalRemainder
                    (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                    (Erdos390.Full.ArithmeticModel.yNat n) u))
                (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperHeadGap W r0) (16 : Real)) := by sorry

-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
-- name    : Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:59:29.381857+00:00
-- url     : https://prove2.me/theorems/d5991346-7595-4eb2-9c0c-a7597ca0865e
-- title:
--   Short-interval freezing and endpoint errors share one cubic-logarithmic rate
-- statement:
--   Let $Z,C,D,a\ge0$, $\ell\ge1$, and $s\ge\ell/5$. Suppose $0\le v\le2aZ/\ell+1$. Then
--
--   $$\frac{vC}{s}\frac D{\ell^2}+\frac Cs\le\bigl(5CD(2a+1)+5C\bigr)\left(\frac Z{\ell^3}+1\right).$$
--
--   The two terms are the freezing displacement loss and a unit endpoint correction for a short deep interval.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalFourFiveDeepIntervalEstimateConnector.lean#L35-L134

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le :
∀ {Z ell logY literal C D a : Real},
  LE.le.{0} (0 : Real) Z →
    LE.le.{0} (1 : Real) ell →
      LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) ell) logY →
        LE.le.{0} (0 : Real) C →
          LE.le.{0} (0 : Real) D →
            LE.le.{0} (0 : Real) a →
              LE.le.{0} literal
                  (HAdd.hAdd.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) a) Z) ell) (1 : Real)) →
                LE.le.{0} (0 : Real) literal →
                  LE.le.{0}
                    (HAdd.hAdd.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} literal logY) C)
                        (HDiv.hDiv.{0, 0, 0} D (HPow.hPow.{0, 0, 0} ell (2 : Nat))))
                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C logY) (1 : Real)))
                    (HMul.hMul.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (5 : Real) C) D)
                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) a) (1 : Real)))
                        (HMul.hMul.{0, 0, 0} (5 : Real) C))
                      (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} ell (3 : Nat))) (1 : Real))) := by sorry

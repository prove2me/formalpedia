-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_roughCanonicalRawPrimePowerColumnResidual_le
-- name    : Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalRawPrimePowerColumnResidual_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:52:46.525775+00:00
-- url     : https://prove2.me/theorems/37dde662-28e4-4901-8147-eb4743a483ba
-- title:
--   Balanced cancellation in one raw prime-power column
-- statement:
--   Let $Kh\le n$, let $p>W$ be prime, and let $k$ be a natural exponent. Suppose real coefficients satisfy $$d_W\left(\alpha Kh+\frac\beta\ell(n-Kh)\right)=h.$$ Then the canonical raw prime-power column residual obeys
--
--   $$|R_{p,k}|\le1+|\alpha|(Q_W+1)+|\beta/\ell|(Q_W+1).$$
--
--   The bound is uniform in the prime-power exponent and leaves only literal counting errors.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector.lean#L292-L413

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_010

theorem Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalRawPrimePowerColumnResidual_le :
∀ {W n h K p k : Nat} {alpha beta ell : Real},
  LE.le.{0} (HMul.hMul.{0, 0, 0} K h) n →
    Eq.{1}
        (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughHeadDensity W)
          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} alpha ↑(HMul.hMul.{0, 0, 0} K h))
            (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} beta ell) ↑(HSub.hSub.{0, 0, 0} n (HMul.hMul.{0, 0, 0} K h)))))
        ↑h →
      Nat.Prime p →
        LT.lt.{0} W p →
          LE.le.{0}
            (abs.{0}
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRawPrimePowerColumnResidual W n h K alpha beta ell
                p k))
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0} (1 : Real)
                (HMul.hMul.{0, 0, 0} (abs.{0} alpha)
                  (HAdd.hAdd.{0, 0, 0} ↑(Erdos390.WholePaper.roughHeadModulus W) (1 : Real))))
              (HMul.hMul.{0, 0, 0} (abs.{0} (HDiv.hDiv.{0, 0, 0} beta ell))
                (HAdd.hAdd.{0, 0, 0} ↑(Erdos390.WholePaper.roughHeadModulus W) (1 : Real)))) := by sorry

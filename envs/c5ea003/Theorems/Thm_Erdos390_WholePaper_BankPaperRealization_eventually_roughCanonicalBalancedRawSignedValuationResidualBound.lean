-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_roughCanonicalBalancedRawSignedValuationResidualBound
-- name    : Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedRawSignedValuationResidualBound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:58:18.336271+00:00
-- url     : https://prove2.me/theorems/5f96b937-f7e8-41d9-863f-fd718aaa2898
-- title:
--   Paper-rate bound for the raw signed valuation residual
-- statement:
--   Write $L=\log n$, $N=n/L$, $Y=\lfloor n^{2/9}\rfloor$, and $h=\mathrm{upperTailLength}(c,n)$. Fix $W,K_0$, $c>0$, and any real $\beta$. Use the head-compatible raw weight with the prescribed balanced alpha at rough level $K_0+1$. Let $C=\mathrm{roughCanonicalBalancedRawSignedValuationConstant}(W,K_0,c,\beta)$. Then eventually, simultaneously for all primes $W<p\le Y$,
--
--   $$|\mathrm{rawSignedValuationResidual}(p)|\le C\frac{N}{pL}.$$
--
--   This gives the required reciprocal-prime paper rate before exceptional and guard corrections.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector.lean#L588-L746

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010

theorem Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedRawSignedValuationResidualBound :
∀ (W K0 : Nat) {c beta : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ᶠ (n : Nat) in Filter.atTop.{0},
      ∀ (p : Nat),
        Nat.Prime p →
          LT.lt.{0} W p →
            LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalBalancedRawSignedValuationResidualBound W n K0 c
                beta p
                (HDiv.hDiv.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0}
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalBalancedRawSignedValuationConstant W K0 c
                      beta)
                    (Erdos390.WholePaper.secondOrderScale n))
                  (HMul.hMul.{0, 0, 0} (↑p) (Erdos390.Full.Scale.L n))) := by sorry

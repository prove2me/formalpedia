-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber
-- name    : Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:21:15.626991+00:00
-- url     : https://prove2.me/theorems/1451137e-26c0-4c6e-9a82-bba783746386
-- title:
--   The core-chamber estimate implies the exceptional paper rate
-- statement:
--   Write $L=\log n$, $N=n/L$, $Y=\lfloor n^{2/9}\rfloor$, and $h=\mathrm{upperTailLength}(c,n)$. Fix $W,K$, $c>0$, $0<\delta_*<1/18$, any real $\beta$, and nonnegative deep, cutoff, and variation constants $C_d,C_c,V$. Assume the eventual signed exceptional core-chamber estimate for the balanced head-compatible raw weight, with these same constants. Set $C=\mathrm{roughCanonicalSignedExceptionalCoreBoundConstant}(W,c,\delta_*,C_d,C_c,V)$. Then eventually, uniformly for primes $W<p\le Y$,
--
--   $$|\mathrm{signedExceptionalResidual}(p)|\le C\frac{N}{pL}.$$
--
--   The chamber is the isolated analytic input; all remaining valuation ledgers and asymptotic absorptions are performed here.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalCoreFirst.lean#L1289-L1503

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber :
∀ {W K : Nat} {c deltaStar beta deepConstant cutoffConstant variationConstant : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      LT.lt.{0} deltaStar (1 / 18 : Real) →
        LE.le.{0} (0 : Real) deepConstant →
          LE.le.{0} (0 : Real) cutoffConstant →
            LE.le.{0} (0 : Real) variationConstant →
              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalCoreChamberEventually W K c
                  deltaStar beta deepConstant cutoffConstant variationConstant →
                ∀ᶠ (n : Nat) in Filter.atTop.{0},
                  ∀ (p : Nat),
                    Nat.Prime p →
                      LT.lt.{0} W p →
                        LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
                          Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalResidualBound n
                            (Erdos390.WholePaper.upperTailLength c n) K deltaStar
                            (Erdos390.WholePaper.roughHeadCompatibleRawWeight W n
                              (Erdos390.WholePaper.upperTailLength c n) K
                              (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n)
                                K beta (Erdos390.Full.Scale.L n))
                              beta (Erdos390.Full.Scale.L n))
                            p
                            (HDiv.hDiv.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0}
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalCoreBoundConstant
                                  W c deltaStar deepConstant cutoffConstant variationConstant)
                                (Erdos390.WholePaper.secondOrderScale n))
                              (HMul.hMul.{0, 0, 0} (↑p) (Erdos390.Full.Scale.L n))) := by sorry

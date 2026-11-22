-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
-- name    : Erdos390.WholePaper.bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:05:56.075243+00:00
-- url     : https://prove2.me/theorems/73c4d120-331a-4169-8d62-28544c74521a
-- title:
--   Exact logarithmic selector defect as a prime-band valuation sum
-- statement:
--   Let $R$ be a bank realization at size $n$ and tail parameter $c$, with a guarded central-anchor certificate, fixed factors, candidate set $A$, and real selector $s$. Let $T$ be its selector tail target and let $d_p=v_p(T)-\sum_{a\in A}s(a)v_p(a)$ be the source selector valuation deficit. Assume this deficit vanishes at every prime outside the medium band $\mathcal P_{n,W}$. Then
--
--   $$\log T-\sum_{a\in A}s(a)\log a=\sum_{p\in\mathcal P_{n,W}}d_p\log p.$$
--
--   This is the finite unique-factorization identity that converts exact logarithmic balance into weighted valuation balance.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNinePostHeightOrdinaryLogLedgerConnector.lean#L89-L211

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_010

theorem Erdos390.WholePaper.bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit :
∀ {c : Real} {depth n W : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed)
  (fixed candidates : Finset.{0} Nat) (selector : Nat → Real),
  @Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand c depth n W left right changed R
      certificate fixed candidates selector →
    @Eq.{1} Real
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (Real.log
          (@Nat.cast.{0} Real Real.instNatCast
            (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget c depth n left right changed
              certificate R fixed)))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid candidates fun (a : Nat) =>
          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (selector a)
            (Real.log (@Nat.cast.{0} Real Real.instNatCast a))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Erdos390.Full.ArithmeticModel.primeBand n W) fun (p : Nat) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Erdos390.WholePaper.bankPaperCanonicalSelectorValuationDeficit c depth n left right changed R certificate
            fixed candidates selector p)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast p))) := by sorry

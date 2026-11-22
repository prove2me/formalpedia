-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
-- name    : Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:53:55.806572+00:00
-- url     : https://prove2.me/theorems/c8cb1ce7-3f14-4086-b7cf-cf94e33c5708
-- title:
--   Charged nonsmooth rows close every high-prime deficit
-- statement:
--   Let a bank realization and guarded anchor certificate be fixed, with selector $s$ on the guarded candidate set. Suppose charged nonsmooth rows are realized, every complete active nonexceptional rough label has postcharge row capacity, and the signed residual target ledger holds at a natural $p>Y=\lfloor n^{2/9}\rfloor$. Then
--
--   $$\mathrm{bankPaperCanonicalSelectorValuationDeficit}(s,p)=0.$$
--
--   This closes the high-prime part of the support condition; primality of $p$ is not an additional hypothesis of this theorem.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalTopFrozenSelectorTailSupportReductionConnector.lean#L518-L672

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt :
∀ {c : Real} {depth n K : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth))
  (deltaStar : Real) (selector : Nat → Real) (p : Nat),
  @LT.lt.{0} Nat instLTNat (Erdos390.Full.ArithmeticModel.yNat n) p →
    @Erdos390.WholePaper.BankPaperCanonicalChargedNonsmoothRowRealization c depth n
        (Erdos390.WholePaper.upperTailLength c n) K
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
          (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
          (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
        (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
          (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
        R certificate deltaStar selector →
      (∀ (label : Nat),
          Erdos390.WholePaper.IsCompleteRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) label →
            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar label →
              @Erdos390.WholePaper.BankPaperRealization.RoughCanonicalPostchargeRowCapacity c depth n
                (Erdos390.WholePaper.upperTailLength c n)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
                R certificate deltaStar K label) →
        @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSignedResidualTargetLedger c depth n R certificate
            deltaStar p →
          @Eq.{1} Real
            (@Erdos390.WholePaper.bankPaperCanonicalSelectorValuationDeficit c depth n
              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
                (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
                (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
              (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
                (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
              R certificate
              (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors n
                (Erdos390.WholePaper.upperTailLength c n) R deltaStar)
              (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet c depth n
                (Erdos390.WholePaper.upperTailLength c n)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R)
                (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) R depth)
                R certificate deltaStar K)
              selector p)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by sorry

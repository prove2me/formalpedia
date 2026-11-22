-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalFourFiveDeepBroadClippingExcess_le
-- name    : Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepBroadClippingExcess_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:58:32.132892+00:00
-- url     : https://prove2.me/theorems/79867bf3-54e3-4603-a4be-78b83733f3f7
-- title:
--   Broad clipping excess on a deep exceptional core
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Let $T$ be the paper exceptional cutoff at exponent $\delta_*$, $R_*$ the real exceptional rough cutoff, and $Z=\lfloor3n/b\rfloor+1$. Set $u_b=\log(2n/b)/\log Y_n$. Assume $n>0$, $L\ge1$, $L\le n^{\delta_*}$, and $1\le b\le\lfloor T/2\rfloor$. Then, with subtraction and quotient inside the parentheses taken in natural numbers,
--
--   $$\max(\lfloor n/b\rfloor,R_*)-\lfloor n/b\rfloor\le Z/L+1.$$
--
--   This retains broad-interval clipping explicitly while bounding its effect at the required scale.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalFourFiveDeepEndpointErrorConnector.lean#L257-L423

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepBroadClippingExcess_le :
∀ {n b : Nat} {deltaStar : Real},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (Erdos390.Full.Scale.L n) →
      @LE.le.{0} Real Real.instLE (Erdos390.Full.Scale.L n)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast n) deltaStar) →
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            b →
          @LE.le.{0} Real Real.instLE
            (@Nat.cast.{0} Real Real.instNatCast
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Max.max.{0} Nat Nat.instMax (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n b)
                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRealExceptionalRoughCutoff n deltaStar))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n b)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalRateScale n b)
                (Erdos390.Full.Scale.L n))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := by sorry

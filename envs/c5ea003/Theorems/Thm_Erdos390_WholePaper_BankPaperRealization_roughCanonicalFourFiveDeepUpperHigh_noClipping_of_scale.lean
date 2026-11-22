-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
-- name    : Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:58:52.87677+00:00
-- url     : https://prove2.me/theorems/c479e0ea-e8bc-4d0f-bf11-dce14676aba0
-- title:
--   No upper or high clipping for deep cores
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Let $T$ be the paper exceptional cutoff at exponent $\delta_*$, $R_*$ the real exceptional rough cutoff, and $Z=\lfloor3n/b\rfloor+1$. Set $u_b=\log(2n/b)/\log Y_n$. Assume $n>0$, $n^{\delta_*}\ge2$, $Kh\le\lfloor n/2\rfloor$, and $1\le b\le\lfloor T/2\rfloor$. Then
--
--   $$R_*\le\lfloor2n/b\rfloor,\qquad R_*\le\lfloor(2n-Kh)/b\rfloor.$$
--
--   Thus taking the maximum with the exceptional rough cutoff changes neither of these quotient endpoints.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalFourFiveDeepEndpointErrorConnector.lean#L98-L204

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

theorem Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale :
∀ {K0 n b : Nat} {c deltaStar : Real},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LE.le.{0} Real Real.instLE
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast n) deltaStar) →
      @LE.le.{0} Nat instLENat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Erdos390.WholePaper.upperTailLength c n))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            b →
          And
            (@LE.le.{0} Nat instLENat
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRealExceptionalRoughCutoff n deltaStar)
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                b))
            (@LE.le.{0} Nat instLENat
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRealExceptionalRoughCutoff n deltaStar)
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Erdos390.WholePaper.upperTailLength c n)))
                b)) := by sorry

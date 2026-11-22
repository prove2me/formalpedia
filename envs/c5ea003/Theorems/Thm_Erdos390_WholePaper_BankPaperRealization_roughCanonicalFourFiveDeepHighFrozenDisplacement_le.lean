-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalFourFiveDeepHighFrozenDisplacement_le
-- name    : Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighFrozenDisplacement_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:58:43.205148+00:00
-- url     : https://prove2.me/theorems/c474272d-76ff-4e7a-b16e-4ac6e30f422f
-- title:
--   Frozen logarithmic displacement on the deep high interval
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Let $T$ be the paper exceptional cutoff at exponent $\delta_*$, $R_*$ the real exceptional rough cutoff, and $Z=\lfloor3n/b\rfloor+1$. Set $u_b=\log(2n/b)/\log Y_n$. Assume $n>0$, $c>0$, $L\ge1$, $\log Y_n\ge L/5$, $h\le2cn/L$, $T\le n/L^2$, $Kh\le\lfloor n/2\rfloor$, and $1\le b\le\lfloor T/2\rfloor$. Let $a$ be the source clipped lower quotient endpoint at $2n-Kh$, and let $d=\lfloor2n/b\rfloor$ be its upper endpoint. Every real $t\in[a,d]$ satisfies
--
--   $$\left|\frac{\log t}{\log Y_n}-u_b\right|\le\frac{D_{\rm high}(K_0,c)}{L^2},$$
--
--   where $D_{\rm high}$ is the source deep-high displacement constant.
--
--   This permits freezing the continuum kernel on a short high interval at one common core coordinate.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalFourFiveDeepDisplacementConnector.lean#L410-L600

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

theorem Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighFrozenDisplacement_le :
∀ {K0 n b : Nat} {c deltaStar : Real},
  LT.lt.{0} (0 : Nat) n →
    LT.lt.{0} (0 : Real) c →
      LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
        LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
            (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
          LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n))
              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) ↑n)
                (Erdos390.Full.Scale.L n)) →
            LE.le.{0} (↑(Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n))
                (HDiv.hDiv.{0, 0, 0} (↑n) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) →
              LE.le.{0}
                  (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.upperTailLength c n))
                  (HDiv.hDiv.{0, 0, 0} n (2 : Nat)) →
                Membership.mem.{0, 0}
                    (Finset.Icc.{0} (1 : Nat)
                      (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) (2 : Nat)))
                    b →
                  ∀ (t : Real),
                    Membership.mem.{0, 0}
                        (Set.Icc.{0}
                          ↑(Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint n
                              deltaStar b
                              (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                  (Erdos390.WholePaper.upperTailLength c n))))
                          ↑(Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint b
                              (HMul.hMul.{0, 0, 0} (2 : Nat) n)))
                        t →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (HDiv.hDiv.{0, 0, 0} (Real.log t) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))
                            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenCoordinate n b)))
                        (HDiv.hDiv.{0, 0, 0}
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighDisplacementConstant
                            K0 c)
                          (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) := by sorry

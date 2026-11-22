-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
-- name    : Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:05:29.123203+00:00
-- url     : https://prove2.me/theorems/b499b252-7db4-4d66-88d6-01058b4995c2
-- title:
--   Assembly of the three frozen deep exceptional interval estimates
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Let $T$ be the paper exceptional cutoff at exponent $\delta_*$, $R_*$ the real exceptional rough cutoff, and $Z=\lfloor3n/b\rfloor+1$. Set $u_b=\log(2n/b)/\log Y_n$. Assume $Y_n\ge2$, $c,P,C\ge0$, $L\ge1$, $\log Y_n\ge L/5$, $h\le2cn/L$, and $h\le n$. Suppose the common endpoint geometry holds, $u_b\in[41/10,47/10]$, and $1\le b\le\lfloor T/2\rfloor$. Assume the mixture kernel and its derivative are bounded by $C$ on this chamber, every geometrically admissible interval has rough-count error at most $PZ/L^3$, and the source deep frozen-displacement and endpoint-length-error packages hold. Write $k_b$ for the kernel at $u_b$ divided by $\log Y_n$. Then
--
--   $$|N_+-k_bh/b|\le C_+(Z/L^3+1),$$
--
--   $$|N_h-k_bKh/b|\le C_h(Z/L^3+1),\qquad |N_b-k_b(n-Kh)_+/b|\le C_b(Z/L^2+1).$$
--
--   The constants are the source deep upper, high, and final broad estimate constants at $(P,C,c)$, $(K_0,P,C,c)$, and $(P,C)$; $(n-Kh)_+$ is natural subtraction.
--
--   This packages the common frozen main term for all three deep intervals while preserving broad clipping.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalFourFiveDeepIntervalEstimateConnector.lean#L640-L899

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

theorem Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs :
∀ {K0 n b : Nat} {c deltaStar P C : Real},
  LE.le.{0} (2 : Nat) (Erdos390.Full.ArithmeticModel.yNat n) →
    LE.le.{0} (0 : Real) c →
      LE.le.{0} (0 : Real) P →
        LE.le.{0} (0 : Real) C →
          LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
              LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n))
                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) ↑n)
                    (Erdos390.Full.Scale.L n)) →
                LE.le.{0} (Erdos390.WholePaper.upperTailLength c n) n →
                  Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar →
                    Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real))
                        (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenCoordinate n b) →
                      Membership.mem.{0, 0}
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalDeepCoreSet deltaStar n)
                          b →
                        (∀ (z : Real),
                            Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real)) z →
                              And
                                (LE.le.{0}
                                  (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernel z))
                                  C)
                                (LE.le.{0}
                                  (abs.{0}
                                    (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernelDerivative
                                      z))
                                  C)) →
                          (∀ (A B : Nat),
                              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                                  n deltaStar b A B →
                                LE.le.{0}
                                  (abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (↑(Finset.card.{0}
                                          (Erdos390.WholePaper.BankPaperRealization.fourFiveRoughInterval
                                            (Erdos390.Full.ArithmeticModel.yNat n) A B)))
                                      (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureIntegralMain
                                        (Erdos390.Full.ArithmeticModel.yNat n) A B)))
                                  (HMul.hMul.{0, 0, 0} P
                                    (HDiv.hDiv.{0, 0, 0}
                                      (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalRateScale
                                        n b)
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (3 : Nat))))) →
                            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
                                K0 n b c deltaStar →
                              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
                                  K0 n b c deltaStar →
                                Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalDeepIntervalEstimate
                                  K0 n b c deltaStar
                                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepUpperEstimateConstant
                                    P C c)
                                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighEstimateConstant
                                    K0 P C c)
                                  (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepBroadFinalEstimateConstant
                                    P C) := by sorry

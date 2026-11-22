-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty
-- name    : Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:59:41.805409+00:00
-- url     : https://prove2.me/theorems/99505007-78b3-40a1-a130-f17cff10ac6d
-- title:
--   Exceptional cutoff interval bounds from geometry or emptiness
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Let $T$ be the paper exceptional cutoff at exponent $\delta_*$, $R_*$ the real exceptional rough cutoff, and $Z=\lfloor3n/b\rfloor+1$. Set $u_b=\log(2n/b)/\log Y_n$. Assume $Y_n\ge2$, $c,P,C_K\ge0$, $L\ge1$, $\log Y_n\ge L/5$, and $h\le2cn/L$. Assume $\lfloor T/2\rfloor<b\le2T$. On $[41/10,47/10]$ assume both the four/five mixture kernel and its derivative have absolute value at most $C_K$. Assume every interval with the source clipped-interval geometry has rough-count error from its continuum integral at most $PZ/L^3$. Require each of the upper, high, and broad physical rough intervals either to satisfy that geometry or to be empty. Then
--
--   $$N_+\le C_+(Z/L^2+1),\qquad N_h\le C_h(Z/L^2+1),\qquad N_b\le C_b(Z/L+1).$$
--
--   Here $N_+,N_h,N_b$ are their cardinalities, and $C_+,C_h,C_b$ are respectively the source cutoff upper, high, and broad estimate constants at $(P,C_K,c)$, $(K_0,P,C_K,c)$, and $(P,C_K)$.
--
--   This handles potentially empty clipped intervals uniformly.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalFourFiveCutoffIntervalPrecursorConnector.lean#L406-L726

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

theorem Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty :
∀ {K0 n b : Nat} {c deltaStar P Ckernel : Real},
  LE.le.{0} (2 : Nat) (Erdos390.Full.ArithmeticModel.yNat n) →
    LE.le.{0} (0 : Real) c →
      LE.le.{0} (0 : Real) P →
        LE.le.{0} (0 : Real) Ckernel →
          LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
              LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n))
                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) ↑n)
                    (Erdos390.Full.Scale.L n)) →
                Membership.mem.{0, 0}
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalCutoffCoreSet deltaStar n) b →
                  (∀ (z : Real),
                      Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real)) z →
                        And
                          (LE.le.{0}
                            (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernel z))
                            Ckernel)
                          (LE.le.{0}
                            (abs.{0}
                              (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernelDerivative z))
                            Ckernel)) →
                    (∀ (A B : Nat),
                        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry n
                            deltaStar b A B →
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
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalRateScale n
                                  b)
                                (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (3 : Nat))))) →
                      And
                          (Or
                            (Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                              n deltaStar b
                              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint n
                                deltaStar b (HMul.hMul.{0, 0, 0} (2 : Nat) n))
                              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint b
                                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                  (Erdos390.WholePaper.upperTailLength c n))))
                            (Eq.{1}
                              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalUpperPhysicalRoughInterval
                                n (Erdos390.WholePaper.upperTailLength c n) deltaStar b)
                              EmptyCollection.emptyCollection.{0}))
                          (And
                            (Or
                              (Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                                n deltaStar b
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint
                                  n deltaStar b
                                  (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                      (Erdos390.WholePaper.upperTailLength c n))))
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint
                                  b (HMul.hMul.{0, 0, 0} (2 : Nat) n)))
                              (Eq.{1}
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalHighPhysicalRoughInterval
                                  n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                  deltaStar b)
                                EmptyCollection.emptyCollection.{0}))
                            (Or
                              (Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalPhysicalIntervalGeometry
                                n deltaStar b
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint
                                  n deltaStar b n)
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint
                                  b
                                  (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                      (Erdos390.WholePaper.upperTailLength c n)))))
                              (Eq.{1}
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalBroadPhysicalRoughInterval
                                  n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                  deltaStar b)
                                EmptyCollection.emptyCollection.{0}))) →
                        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalCutoffIntervalEstimate
                          K0 n b c deltaStar
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveCutoffUpperEstimateConstant P
                            Ckernel c)
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveCutoffHighEstimateConstant K0
                            P Ckernel c)
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveCutoffBroadEstimateConstant P
                            Ckernel) := by sorry

-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_balanced_three_interval_cutoff_le_paperRate
-- name    : Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_cutoff_le_paperRate
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:33:49.690562+00:00
-- url     : https://prove2.me/theorems/4ab8d5a9-87cd-4855-9ed3-b2d0e951e8af
-- title:
--   Balanced three-interval cutoff bound at the paper rate
-- statement:
--   Write $L=\log n$, $N=n/L$, $Y=\lfloor n^{2/9}\rfloor$, $h=\mathrm{upperTailLength}(c,n)$, $Q_W=\mathrm{roughHeadModulus}(W)$, and $d_W=\mathrm{roughHeadDensity}(W)$. Assume $c>0$, $n\ge2$, $L\ge1$, $Z\ge0$, and three nonnegative counts $N_+,N_H,N_B$. Suppose they are bounded by $C_+(Z/L^2+1)$, $C_H(Z/L^2+1)$, and $C_B(Z/L+1)$ respectively, with nonnegative coefficients. Let $g=\mathbf1_{(b,Q_W)=1}$ and $\alpha=\mathrm{roughHeadBalancedAlpha}(W,n,h,K_0+1,\beta,L)$. Set $A=\mathrm{roughBalancedAlphaConstant}(W,K_0,c,\beta)$.
--
--   $$|N_+-g(\alpha N_H+(\beta/L)N_B)|\le(C_++AC_H+|\beta|C_B)(Z/L^2+1).$$
--
--   This is a deterministic adapter: the three interval-count hypotheses remain explicit inputs.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveSignedCoreErrorAdapter.lean#L876-L989

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

theorem Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_cutoff_le_paperRate :
∀ {W K0 n b : Nat} {c beta Nplus Nhigh Nbroad Cplus Chigh Cbroad Z : Real},
  LT.lt.{0} (0 : Real) c →
    LE.le.{0} (2 : Nat) n →
      LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
        LE.le.{0} (0 : Real) Z →
          LE.le.{0} (0 : Real) Nplus →
            LE.le.{0} (0 : Real) Nhigh →
              LE.le.{0} (0 : Real) Nbroad →
                LE.le.{0} Nplus
                    (HMul.hMul.{0, 0, 0} Cplus
                      (HAdd.hAdd.{0, 0, 0}
                        (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) (1 : Real))) →
                  LE.le.{0} Nhigh
                      (HMul.hMul.{0, 0, 0} Chigh
                        (HAdd.hAdd.{0, 0, 0}
                          (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat)))
                          (1 : Real))) →
                    LE.le.{0} Nbroad
                        (HMul.hMul.{0, 0, 0} Cbroad
                          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} Z (Erdos390.Full.Scale.L n)) (1 : Real))) →
                      LE.le.{0} (0 : Real) Cplus →
                        LE.le.{0} (0 : Real) Chigh →
                          LE.le.{0} (0 : Real) Cbroad →
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0} Nplus
                                  (HMul.hMul.{0, 0, 0}
                                    (ite.{1} (Nat.Coprime b (Erdos390.WholePaper.roughHeadModulus W)) (1 : Real)
                                      (0 : Real))
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0}
                                        (Erdos390.WholePaper.roughHeadBalancedAlpha W n
                                          (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                          beta (Erdos390.Full.Scale.L n))
                                        Nhigh)
                                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} beta (Erdos390.Full.Scale.L n))
                                        Nbroad)))))
                              (HMul.hMul.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HAdd.hAdd.{0, 0, 0} Cplus
                                    (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughBalancedAlphaConstant W K0 c beta)
                                      Chigh))
                                  (HMul.hMul.{0, 0, 0} (abs.{0} beta) Cbroad))
                                (HAdd.hAdd.{0, 0, 0}
                                  (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat)))
                                  (1 : Real))) := by sorry

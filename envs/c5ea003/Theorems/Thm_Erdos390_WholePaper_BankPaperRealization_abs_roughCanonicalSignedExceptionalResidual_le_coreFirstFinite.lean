-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
-- name    : Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:51:44.448732+00:00
-- url     : https://prove2.me/theorems/da239f41-70c8-4044-a354-69115c66d863
-- title:
--   Finite core-first bound for the signed exceptional residual
-- statement:
--   Write $L=\log n$, $N=n/L$, $Y=\lfloor n^{2/9}\rfloor$, $h=\mathrm{upperTailLength}(c,n)$, $Q_W=\mathrm{roughHeadModulus}(W)$, and $d_W=\mathrm{roughHeadDensity}(W)$. For this finite statement allow arbitrary $h\le n$ and $n\ge1$. Assume $\delta_*\ge0$, $p>W$ prime, $p\le Y$, and $X=\mathrm{tangentPaperExceptionalCutoff}(\delta_*,n)\ge2$. Put $B=\lfloor X/2\rfloor$. Suppose the core-chamber estimate holds with nonnegative constants $C_d,C_c,V$: deep core mass equals $(h/\log Y)(1-\mathbf1_{(b,Q_W)=1}/d_W)\,w_b+e_b$, with $|e_b|\le C_d(n/(bL^3)+1)$; cutoff core mass is at most $C_c(n/(bL^2)+1)$ in absolute value; and the discrete variation of $w_{p^km}$ is at most $V/p^k$ on each relevant truncated progression. Then
--
--   $$|R_{\rm exc}(p)|\le\frac h{\log Y}\frac{2Q_WV}{d_Wp}+\frac{C_dn}{L^3}\frac{2(1+\log B)}p+\frac{2C_dB}p+\frac{8C_cn}{pL^2}+\frac{4C_cX}p.$$
--
--   The estimate exposes periodic cancellation, deep errors, and cutoff errors separately before asymptotic absorption.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSignedExceptionalCoreFirst.lean#L965-L1119

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

theorem Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite :
∀ {W n h K p : Nat} {deltaStar : Real} {rawWeight kernelWeight coreError : Nat → Real}
  {deepConstant cutoffConstant variationConstant : Real},
  LE.le.{0} (0 : Real) deltaStar →
    LE.le.{0} (1 : Nat) n →
      LE.le.{0} h n →
        Nat.Prime p →
          LT.lt.{0} W p →
            LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
              LE.le.{0} (2 : Nat) (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) →
                LE.le.{0} (0 : Real) deepConstant →
                  LE.le.{0} (0 : Real) cutoffConstant →
                    LE.le.{0} (0 : Real) variationConstant →
                      Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalCoreChamberEstimate W n h
                          K deltaStar rawWeight kernelWeight coreError deepConstant cutoffConstant variationConstant →
                        LE.le.{0}
                          (abs.{0}
                            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalResidual n h K
                              deltaStar rawWeight p))
                          (HAdd.hAdd.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HDiv.hDiv.{0, 0, 0} (↑h) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))
                                    (HDiv.hDiv.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                          (HDiv.hDiv.{0, 0, 0} (↑(Erdos390.WholePaper.roughHeadModulus W))
                                            (Erdos390.WholePaper.roughHeadDensity W)))
                                        variationConstant)
                                      ↑p))
                                  (HMul.hMul.{0, 0, 0}
                                    (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} deepConstant ↑n)
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (3 : Nat)))
                                    (HDiv.hDiv.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                        (HAdd.hAdd.{0, 0, 0} (1 : Real)
                                          (Real.log
                                            ↑(HDiv.hDiv.{0, 0, 0}
                                                (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                                                (2 : Nat)))))
                                      ↑p)))
                                (HMul.hMul.{0, 0, 0} deepConstant
                                  (HDiv.hDiv.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (2 : Real)
                                      ↑(HDiv.hDiv.{0, 0, 0}
                                          (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) (2 : Nat)))
                                    ↑p)))
                              (HMul.hMul.{0, 0, 0}
                                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} cutoffConstant ↑n)
                                  (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat)))
                                (HDiv.hDiv.{0, 0, 0} (8 : Real) ↑p)))
                            (HMul.hMul.{0, 0, 0} cutoffConstant
                              (HDiv.hDiv.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (4 : Real)
                                  ↑(Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n))
                                ↑p))) := by sorry

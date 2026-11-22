-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerTailRow_eventually_tail_row_le
-- name    : Erdos390.Full.PaperPrimePowerTailRow.eventually_tail_row_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:23:47.993499+00:00
-- url     : https://prove2.me/theorems/0e870213-14ee-44de-aff7-7766b40fd037
-- title:
--   A common bound for all outside-chamber residual rows
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix $G\ge0$, $C>0$, and integer $W>1$. Use the four explicit outside-chamber error functions $e^{JI},e^{IJ},e^{JJ},e^D$ of the prime-power displays, and actual cutoff sets $R_p=\{2,\ldots,\mathrm{actualExponentCutoff}(C,n,p)\}$. Put $T=G+G^2$, $K=\mathrm{cutoffScale}(W)L$, and $H=\sum_{W<q\le Y}1/q$. For all sufficiently large $n$, uniformly for each band prime $p$,
--
--   $$p\left[\sum_{q\ne p}\left(\sum_{r\in R_p}e^{JI}_{pqr}+\sum_{s\in R_q}e^{IJ}_{pqs}+\sum_{r\in R_p,s\in R_q}e^{JJ}_{pqrs}\right)+3\sum_{r\in R_p}(2r-3)e^D_{pr}\right]\le T\frac K Y(H+1)+T\frac{K^2}{Y^{2/3}}+6G\frac{K^2}{Y^2}.$$
--
--   A single uniform scalar now controls the complete residual ledger of every selected row.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerTailRow.lean#L211-L389

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

theorem Erdos390.Full.PaperPrimePowerTailRow.eventually_tail_row_le :
∀ (G C : Real) (W : Nat),
  LE.le.{0} (0 : Real) G →
    LT.lt.{0} (0 : Real) C →
      LT.lt.{0} (1 : Nat) W →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (p : Nat),
            Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
              LE.le.{0}
                (HMul.hMul.{0, 0, 0} (↑p)
                  (HAdd.hAdd.{0, 0, 0}
                    (∑ q ∈ Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p,
                      HAdd.hAdd.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0}
                          (∑
                            r ∈
                              Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n p),
                            Erdos390.Full.PaperPrimePowerFourDisplays.eJI G n p q r)
                          (∑
                            s ∈
                              Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n q),
                            Erdos390.Full.PaperPrimePowerFourDisplays.eIJ G n p q s))
                        (∑
                          r ∈
                            Erdos390.Full.ArithmeticModel.highExponents
                              (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n p),
                          ∑
                            s ∈
                              Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n q),
                            Erdos390.Full.PaperPrimePowerFourDisplays.eJJ G n p q r s))
                    (HMul.hMul.{0, 0, 0} (3 : Real)
                      (∑
                        r ∈
                          Erdos390.Full.ArithmeticModel.highExponents
                            (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n p),
                        HMul.hMul.{0, 0, 0} (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)))
                          (Erdos390.Full.PaperPrimePowerFourDisplays.eD G n p r)))))
                (Erdos390.Full.PaperPrimePowerTailRow.tailRowMajorant G W n) := by sorry

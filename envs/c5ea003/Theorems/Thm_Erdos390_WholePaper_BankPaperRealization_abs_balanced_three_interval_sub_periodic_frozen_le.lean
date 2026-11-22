-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_balanced_three_interval_sub_periodic_frozen_le
-- name    : Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_sub_periodic_frozen_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:50:17.950007+00:00
-- url     : https://prove2.me/theorems/e23470f7-bacb-4360-986c-0d1ef49f0c3e
-- title:
--   Balanced freezing preserves the signed periodic main term
-- statement:
--   Let $W,K_0,n,h,b$ be natural numbers with $(K_0+1)h>0$. Put $g=\mathbf1_{(b,Q_W)=1}$, $\alpha=\mathrm{roughHeadBalancedAlpha}(W,n,h,K_0+1,\beta,\ell)$, and $k=\mathrm{kernelValue}/\mathrm{logY}$. Suppose the three counts differ from $kh/b$, $k(K_0+1)h/b$, and $k(n-(K_0+1)h)/b$ by at most $E_+,E_H,E_B$, respectively; the subtraction in the last numerator is natural subtraction. Then
--
--   $$\left|N_+-g\left(\alpha N_H+\frac\beta\ell N_B\right)-\frac{kh}{b}\left(1-\frac g{d_W}\right)\right|\le E_++|\alpha|E_H+|\beta/\ell|E_B.$$
--
--   The signed periodic leading term is retained exactly rather than bounded separately.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveSignedCoreErrorAdapter.lean#L609-L755

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

theorem Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_sub_periodic_frozen_le :
∀ {W K0 n h b : Nat} {beta ell logY kernelValue Nplus Nhigh Nbroad Eplus Ehigh Ebroad : Real},
  LT.lt.{0} (0 : Nat) (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) h) →
    LE.le.{0}
        (abs.{0}
          (HSub.hSub.{0, 0, 0} Nplus
            (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY) (HDiv.hDiv.{0, 0, 0} ↑h ↑b))))
        Eplus →
      LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0} Nhigh
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY)
                (HDiv.hDiv.{0, 0, 0} ↑(HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) h) ↑b))))
          Ehigh →
        LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0} Nbroad
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY)
                  (HDiv.hDiv.{0, 0, 0}
                    ↑(HSub.hSub.{0, 0, 0} n (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) h)) ↑b))))
            Ebroad →
          LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0}
                (HSub.hSub.{0, 0, 0} Nplus
                  (HMul.hMul.{0, 0, 0}
                    (ite.{1} (Nat.Coprime b (Erdos390.WholePaper.roughHeadModulus W)) (1 : Real) (0 : Real))
                    (HAdd.hAdd.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0}
                        (Erdos390.WholePaper.roughHeadBalancedAlpha W n h (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta ell)
                        Nhigh)
                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} beta ell) Nbroad))))
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY) (HDiv.hDiv.{0, 0, 0} ↑h ↑b))
                  (Erdos390.WholePaper.BankPaperRealization.roughHeadPeriodicCoreCoefficient W b))))
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0} Eplus
                (HMul.hMul.{0, 0, 0}
                  (abs.{0}
                    (Erdos390.WholePaper.roughHeadBalancedAlpha W n h (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta ell))
                  Ehigh))
              (HMul.hMul.{0, 0, 0} (abs.{0} (HDiv.hDiv.{0, 0, 0} beta ell)) Ebroad)) := by sorry

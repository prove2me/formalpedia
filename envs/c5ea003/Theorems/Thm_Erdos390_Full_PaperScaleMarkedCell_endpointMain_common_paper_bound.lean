-- Prove2me | Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_endpointMain_common_paper_bound
-- name    : Erdos390.Full.PaperScaleMarkedCell.endpointMain_common_paper_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:23:49.47821+00:00
-- url     : https://prove2.me/theorems/9487e2a5-1dc8-4e5d-8085-ca6ee2500310
-- title:
--   Replacing a floored endpoint by the common Dickman coordinate
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix $C>0$ and integers $n>1$, $g,d>0$. Set $r=Cn/(gd)$ and $X=\lfloor Cn\rfloor/(gd)$, with the latter quotient taken in the natural numbers. Assume $d\le Y^4$, $y\ge2$, $L/5\le\log Y$, $r\ge4$, $r\ge L$, and $\log X\le5\log Y$. The endpoint main term is $X\rho(\log X/\log Y)$.
--
--   $$\left|X\rho\!\left(\frac{\log X}{\log Y}\right)-r\rho(v_d)\right|\le\left(2+5(\log2+|\log C-\log g|)+\frac{45}{2}\log2\right)\frac rL.$$
--
--   This makes all fixed head-divisor endpoints share the same Dickman translate.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperScaleEndpoint.lean#L260-L402

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.PaperScaleMarkedCell.endpointMain_common_paper_bound :
∀ (C : Real) (n g d : Nat),
  LT.lt.{0} (0 : Real) C →
    LT.lt.{0} (1 : Nat) n →
      LT.lt.{0} (0 : Nat) g →
        LT.lt.{0} (0 : Nat) d →
          LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
            LE.le.{0} (2 : Real) (Erdos390.Full.ArithmeticModel.y n) →
              LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                  (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
                LE.le.{0} (4 : Real) (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d)) →
                  LE.le.{0} (Erdos390.Full.Scale.L n)
                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d)) →
                    LE.le.{0}
                        (Real.log
                          ↑(HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound C n)
                              (HMul.hMul.{0, 0, 0} g d)))
                        (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n))) →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.StructuredCellAsymptotic.endpointMain
                              (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                (HMul.hMul.{0, 0, 0} g d))
                              (Erdos390.Full.ArithmeticModel.yNat n))
                            (HMul.hMul.{0, 0, 0}
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d))
                              (Erdos390.Full.DickmanBasic.rho
                                (Erdos390.Full.PaperScaleMarkedCell.paperDivisorCoordinate n d)))))
                        (HDiv.hDiv.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (2 : Real)
                                (HMul.hMul.{0, 0, 0} (5 : Real)
                                  (HAdd.hAdd.{0, 0, 0} (Real.log (2 : Real))
                                    (abs.{0} (HSub.hSub.{0, 0, 0} (Real.log C) (Real.log ↑g))))))
                              (HMul.hMul.{0, 0, 0} (45 / 2 : Real) (Real.log (2 : Real))))
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d)))
                          (Erdos390.Full.Scale.L n)) := by sorry

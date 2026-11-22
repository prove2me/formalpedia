-- Prove2me | Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_headDivisorMain_sum_sub_common_le
-- name    : Erdos390.Full.PaperScaleMarkedCell.headDivisorMain_sum_sub_common_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:29:19.833142+00:00
-- url     : https://prove2.me/theorems/c3c89ba7-3ae3-4c61-81d3-9eb9ae34edbd
-- title:
--   Summed head-divisor endpoint replacement
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix a head pattern $P$ with factor $f$ and modulus $m$, positive $A,B$, and integers $n>1,d>0$. Assume $d\le Y^4$, $y\ge2$, and $L/5\le\log Y$. For every $a\mid m$ and $C\in\{A,B\}$ assume $Cn/(fad)\ge\max(4,L)$ and $\log(\lfloor Cn\rfloor/(fad))\le5\log Y$, using natural division. Put $E(C,g)=2+5(\log2+|\log C-\log g|)+(45/2)\log2$ and $F_P(C)=\sum_{a\mid m}|\mu(a)|E(C,fa)C/(fa)$. Let $H_a$ be the Möbius-weighted difference of the two endpoint main terms at $\lfloor An\rfloor/(fad)$ and $\lfloor Bn\rfloor/(fad)$.
--
--   $$\left|\sum_{a\mid m}H_a-\sum_{a\mid m}\mu(a)\frac{(B-A)n}{fad}\rho(v_d)\right|\le\frac{(F_P(B)+F_P(A))n}{dL}.$$
--
--   This is the error estimate that permits head inclusion–exclusion to close on one common main term.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperScaleMarkedCell.lean#L266-L405

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.PaperScaleMarkedCell.headDivisorMain_sum_sub_common_le :
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A B : Real} {n d : Nat},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} (0 : Real) B →
      LT.lt.{0} (1 : Nat) n →
        LT.lt.{0} (0 : Nat) d →
          LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
            LE.le.{0} (2 : Real) (Erdos390.Full.ArithmeticModel.y n) →
              LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                  (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
                (∀ (a : Nat),
                    Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                      And
                        (LE.le.{0} (4 : Real)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} A ↑n)
                            ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                d)))
                        (LE.le.{0} (Erdos390.Full.Scale.L n)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} A ↑n)
                            ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                d)))) →
                  (∀ (a : Nat),
                      Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                        And
                          (LE.le.{0} (4 : Real)
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑n)
                              ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                  d)))
                          (LE.le.{0} (Erdos390.Full.Scale.L n)
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑n)
                              ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                  d)))) →
                    (∀ (a : Nat),
                        Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                          LE.le.{0}
                            (Real.log
                              ↑(HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d)))
                            (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))) →
                      (∀ (a : Nat),
                          Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                            LE.le.{0}
                              (Real.log
                                ↑(HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound B n)
                                    (HMul.hMul.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d)))
                              (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))) →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (∑ a ∈ Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P),
                                Erdos390.Full.StructuredCellAsymptotic.headDivisorMain P
                                  (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                  (Erdos390.Full.ArithmeticModel.physicalBound B n)
                                  (Erdos390.Full.ArithmeticModel.yNat n) d a)
                              (∑ a ∈ Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P),
                                HMul.hMul.{0, 0, 0} (↑(ArithmeticFunction.moebius a))
                                  (HSub.hSub.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑n)
                                        ↑(HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d))
                                      (Erdos390.Full.DickmanBasic.rho
                                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisorCoordinate n d)))
                                    (HMul.hMul.{0, 0, 0}
                                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} A ↑n)
                                        ↑(HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d))
                                      (Erdos390.Full.DickmanBasic.rho
                                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisorCoordinate n d)))))))
                          (HDiv.hDiv.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PaperScaleMarkedCell.endpointFamilyCoefficient P B)
                                (Erdos390.Full.PaperScaleMarkedCell.endpointFamilyCoefficient P A))
                              ↑n)
                            (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n))) := by sorry

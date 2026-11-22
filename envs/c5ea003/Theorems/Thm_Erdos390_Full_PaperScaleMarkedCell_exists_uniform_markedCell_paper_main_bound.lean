-- Prove2me | Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
-- name    : Erdos390.Full.PaperScaleMarkedCell.exists_uniform_markedCell_paper_main_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:51:05.187741+00:00
-- url     : https://prove2.me/theorems/896cb47d-be3a-492c-bade-41553cf735cc
-- title:
--   Uniform paper-scale marked-cell count
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix a head pattern $P$ and $0<A<B$. Write $h_P=\varphi(P.\mathrm{modulus})/(P.\mathrm{factor}\,P.\mathrm{modulus})$. There are $K>0,N_0$ such that for $n\ge N_0$ and every positive $d\le Y^4$ with all prime factors at most $Y$ and coprime to the head modulus, the marked cell $S_d$ in the physical interval with endpoints $\lfloor An\rfloor,\lfloor Bn\rfloor$ satisfies
--
--   $$\left|\#S_d-h_P\frac{(B-A)n}{d}\rho(v_d)\right|\le\frac{Kn}{dL}.$$
--
--   All constants depend only on the fixed physical interval and head pattern, so the divisor may vary throughout the four-mark range.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperScaleMarkedCell.lean#L553-L717

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.PaperScaleMarkedCell.exists_uniform_markedCell_paper_main_bound :
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A B : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A B →
      ∃ K,
        And (LT.lt.{0} (0 : Real) K)
          (∃ N₀,
            ∀ {n d : Nat},
              LE.le.{0} N₀ n →
                LT.lt.{0} (0 : Nat) d →
                  LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                    Membership.mem.{0, 0}
                        (Nat.smoothNumbers (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (1 : Nat))) d →
                      Nat.Coprime d (Erdos390.Full.HeadPattern.Pattern.modulus P) →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (↑(Finset.card.{0}
                                  (Erdos390.Full.StructuredCells.markedCell P
                                    (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                    (Erdos390.Full.ArithmeticModel.physicalBound B n)
                                    (Erdos390.Full.ArithmeticModel.yNat n) d)))
                              (Erdos390.Full.PaperScaleMarkedCell.paperMarkedMain P A B n d)))
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} K ↑n)
                            (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n)))) := by sorry

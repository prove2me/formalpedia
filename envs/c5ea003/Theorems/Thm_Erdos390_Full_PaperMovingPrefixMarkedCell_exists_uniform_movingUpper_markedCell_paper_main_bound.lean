-- Prove2me | Theorems.Thm_Erdos390_Full_PaperMovingPrefixMarkedCell_exists_uniform_movingUpper_markedCell_paper_main_bound
-- name    : Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingUpper_markedCell_paper_main_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:50:27.55643+00:00
-- url     : https://prove2.me/theorems/c687e247-ff93-485f-b4eb-aae8480b418b
-- title:
--   Uniform marked-cell count with a moving upper endpoint
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. For a head pattern $P$, let $S_P(A,C;n)$ be the positive $Y_n$-smooth integers in $(\lfloor An\rfloor,\lfloor Cn\rfloor]$ having exactly the valuations prescribed by $P$. Fix a pattern $P$ and $0<A<C$. Uniformly for integers $k,d$ with $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$, $0<d\le Y_n^4$, all prime factors of $d$ at most $Y_n$, and $\gcd(d,\operatorname{modulus}(P))=1$, there are $K>0$ and $N_0$ such that for $n\ge N_0$,
--
--   $$\left|\#\{m\in S_P(A,k/n;n):d\mid m\}-M_P(A,k/n;n,d)\right|\le\frac{Kn}{dL_n}.$$
--
--   Here $M_P$ is the paper marked-count main term (`paperMarkedMain`), evaluated at the exact upper scale $k/n$.
--
--   Both the constant and the threshold are independent of the moving integer endpoint and marked modulus.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperMovingPrefixMarkedCell.lean#L170-L432

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingUpper_markedCell_paper_main_bound :
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      ∃ K,
        And (LT.lt.{0} (0 : Real) K)
          (∃ N₀,
            ∀ {n k d : Nat},
              LE.le.{0} N₀ n →
                LT.lt.{0} (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                  LE.le.{0} k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                    LT.lt.{0} (0 : Nat) d →
                      LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                        Membership.mem.{0, 0}
                            (Nat.smoothNumbers (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (1 : Nat)))
                            d →
                          Nat.Coprime d (Erdos390.Full.HeadPattern.Pattern.modulus P) →
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0}
                                  (↑(Finset.card.{0}
                                      (Erdos390.Full.StructuredCells.markedCell P
                                        (Erdos390.Full.ArithmeticModel.physicalBound A n) k
                                        (Erdos390.Full.ArithmeticModel.yNat n) d)))
                                  (Erdos390.Full.PaperScaleMarkedCell.paperMarkedMain P A
                                    (Erdos390.Full.PaperMovingPrefixMarkedCell.prefixScale n k) n d)))
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} K ↑n)
                                (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n)))) := by sorry

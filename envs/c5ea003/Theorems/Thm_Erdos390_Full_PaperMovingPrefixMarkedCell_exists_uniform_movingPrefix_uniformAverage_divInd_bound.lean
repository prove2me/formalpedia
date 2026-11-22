-- Prove2me | Theorems.Thm_Erdos390_Full_PaperMovingPrefixMarkedCell_exists_uniform_movingPrefix_uniformAverage_divInd_bound
-- name    : Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_uniformAverage_divInd_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:19:39.530971+00:00
-- url     : https://prove2.me/theorems/451f01e6-5cde-43eb-9c9b-92fcaae1e513
-- title:
--   Uniform joint divisibility and moving-prefix probability
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. For a head pattern $P$, let $S_P(A,C;n)$ be the positive $Y_n$-smooth integers in $(\lfloor An\rfloor,\lfloor Cn\rfloor]$ having exactly the valuations prescribed by $P$. Fix a pattern $P$ and $0<A<C$. Uniformly for integers $k,d$ with $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$, $0<d\le Y_n^4$, all prime factors of $d$ at most $Y_n$, and $\gcd(d,\operatorname{modulus}(P))=1$, there are $K>0,N_0$ such that for $n\ge N_0$ the full cell $S=S_P(A,C;n)$ is nonempty and
--
--   $$\left|\mathbb E_S[\mathbf1_{d\mid m}\mathbf1_{m\le k}]-\frac{k/n-A}{C-A}D_n(d)\right|\le\frac{K}{dL_n}.$$
--
--   The expectation is uniform on $S$, and $D_n(d)$ denotes the normalized paper divisibility main term (`paperDivisibilityMain`).
--
--   This converts moving marked counts to probabilities on one fixed cell.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperMovingPrefixMarkedCell.lean#L560-L692

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_uniformAverage_divInd_bound :
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
                            have S :=
                              Erdos390.Full.StructuredCells.structuredCell P
                                (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                (Erdos390.Full.ArithmeticModel.yNat n);
                            And (Finset.Nonempty.{0} S)
                              (LE.le.{0}
                                (abs.{0}
                                  (HSub.hSub.{0, 0, 0}
                                    (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S fun m =>
                                      HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticModel.divInd d m)
                                        (ite.{1} (LE.le.{0} m k) (1 : Real) (0 : Real)))
                                    (HMul.hMul.{0, 0, 0}
                                      (Erdos390.Full.PaperMovingPrefixMarkedCell.prefixFraction A C n k)
                                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n d))))
                                (HDiv.hDiv.{0, 0, 0} K (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n))))) := by sorry

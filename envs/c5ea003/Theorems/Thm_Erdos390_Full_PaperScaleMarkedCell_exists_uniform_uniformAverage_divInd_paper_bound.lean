-- Prove2me | Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_uniformAverage_divInd_paper_bound
-- name    : Erdos390.Full.PaperScaleMarkedCell.exists_uniform_uniformAverage_divInd_paper_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:19:56.126912+00:00
-- url     : https://prove2.me/theorems/e3bc23e7-dc40-4318-9972-9377e05ac35b
-- title:
--   Uniform divisor probabilities in a structured cell
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix a head pattern $P$ and $0<A<B$. There exist $K>0,N_0$ such that for $n\ge N_0$ and every positive $Y$-smooth integer $d\le Y^4$ coprime to the head modulus, the structured cell $S$ at physical endpoints $\lfloor An\rfloor,\lfloor Bn\rfloor$ is nonempty and its uniform law satisfies
--
--   $$\left|\mathbb P_S(d\mid m)-\frac{\rho(v_d)}{d\rho(U)}\right|\le\frac{K}{dL}.$$
--
--   This converts uniform counting asymptotics into the finite probability input for tilting.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperScaleMarkedCell.lean#L781-L916

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.PaperScaleMarkedCell.exists_uniform_uniformAverage_divInd_paper_bound :
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
                        And
                          (Finset.Nonempty.{0}
                            (Erdos390.Full.StructuredCells.structuredCell P
                              (Erdos390.Full.ArithmeticModel.physicalBound A n)
                              (Erdos390.Full.ArithmeticModel.physicalBound B n) (Erdos390.Full.ArithmeticModel.yNat n)))
                          (LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (Erdos390.Full.DivisibilityMomentBounds.uniformAverage
                                  (Erdos390.Full.StructuredCells.structuredCell P
                                    (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                    (Erdos390.Full.ArithmeticModel.physicalBound B n)
                                    (Erdos390.Full.ArithmeticModel.yNat n))
                                  (Erdos390.Full.ArithmeticModel.divInd d))
                                (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n d)))
                            (HDiv.hDiv.{0, 0, 0} K (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n))))) := by sorry

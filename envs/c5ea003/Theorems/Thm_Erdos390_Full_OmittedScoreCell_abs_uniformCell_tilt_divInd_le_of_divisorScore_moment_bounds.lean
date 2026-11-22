-- Prove2me | Theorems.Thm_Erdos390_Full_OmittedScoreCell_abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
-- name    : Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:02:28.228284+00:00
-- url     : https://prove2.me/theorems/971076fa-3f2e-45cf-8d02-6778bd80efee
-- title:
--   Explicit moment bounds for the omitted-score tilt
-- statement:
--   Use a nonempty finite uniform cell $S$, divisor score $Q=\sum_{r\in R}\mathbf1_{r\mid m}$, divisor indicator $I=\mathbf1_{D\mid m}$, and $p=\mathbb EI$. Suppose $\beta\ge0$, $|s|\le\beta Q$, $|s|\le K$, and nonnegative $T,M$ satisfy $\mathbb EQ\le T$, $\mathbb E(IQ)\le M$, and $e^K\beta T<1$. For the exponential tilt by $s$,
--
--   $$|\mathbb E_sI-p|\le\frac{e^K\beta M+e^Kp\beta T}{1-e^K\beta T}.$$
--
--   This deterministic form allows common-multiple estimates to be inserted directly.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/OmittedScoreCell.lean#L242-L361

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds :
∀ (S R : Finset.{0} Nat) (hS : Finset.Nonempty.{0} S) (D : Nat) (score : Nat → Real)
  {K beta totalBound markedBound : Real},
  LE.le.{0} (0 : Real) beta →
    (∀ (m : Nat),
        Membership.mem.{0, 0} S m →
          LE.le.{0} (abs.{0} (score m))
            (HMul.hMul.{0, 0, 0} beta (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m))) →
      (∀ (m : Nat), Membership.mem.{0, 0} S m → LE.le.{0} (abs.{0} (score m)) K) →
        LE.le.{0}
            (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
              (Erdos390.Full.DivisibilityMomentBounds.divisorScore R))
            totalBound →
          LE.le.{0}
              (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S fun m =>
                HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticModel.divInd D m)
                  (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m))
              markedBound →
            LE.le.{0} (0 : Real) totalBound →
              LE.le.{0} (0 : Real) markedBound →
                LT.lt.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta) totalBound) (1 : Real) →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.FiniteProbability.expect.{0}
                          (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                            (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun m => score ↑m)
                          fun m => Erdos390.Full.ArithmeticModel.divInd D ↑m)
                        (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                          (Erdos390.Full.ArithmeticModel.divInd D))))
                    (HDiv.hDiv.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta) markedBound)
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (Real.exp K)
                            (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                              (Erdos390.Full.ArithmeticModel.divInd D)))
                          (HMul.hMul.{0, 0, 0} beta totalBound)))
                      (HSub.hSub.{0, 0, 0} (1 : Real)
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta) totalBound))) := by sorry

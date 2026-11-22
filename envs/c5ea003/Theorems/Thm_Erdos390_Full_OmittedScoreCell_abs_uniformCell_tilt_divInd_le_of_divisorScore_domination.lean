-- Prove2me | Theorems.Thm_Erdos390_Full_OmittedScoreCell_abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
-- name    : Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:50:03.493231+00:00
-- url     : https://prove2.me/theorems/f0b9ab53-2edd-4421-a3ea-1721db5392be
-- title:
--   Divisibility under a divisor-dominated exponential tilt
-- statement:
--   Let $S$ be a nonempty finite set of natural numbers, $R$ a finite divisor set, and $D$ a natural number. Under the uniform law on $S$, write $I=\mathbf1_{D\mid m}$, $Q=\sum_{r\in R}\mathbf1_{r\mid m}$, and $p=\mathbb E I$. Suppose the real score satisfies $|s(m)|\le\beta Q(m)$ and $|s(m)|\le K$ on $S$, and $e^K\beta\mathbb EQ<1$. Let $\mathbb E_s$ denote expectation after weighting by $e^s$.
--
--   $$|\mathbb E_s I-p|\le\frac{e^K\beta\mathbb E(IQ)+e^Kp\beta\mathbb EQ}{1-e^K\beta\mathbb EQ}.$$
--
--   Only two divisor-score moments remain to be estimated arithmetically.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/OmittedScoreCell.lean#L96-L240

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_domination :
∀ (S R : Finset.{0} Nat) (hS : Finset.Nonempty.{0} S) (D : Nat) (score : Nat → Real) {K beta : Real},
  (∀ (m : Nat),
      Membership.mem.{0, 0} S m →
        LE.le.{0} (abs.{0} (score m))
          (HMul.hMul.{0, 0, 0} beta (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m))) →
    (∀ (m : Nat), Membership.mem.{0, 0} S m → LE.le.{0} (abs.{0} (score m)) K) →
      LT.lt.{0}
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta)
            (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
              (Erdos390.Full.DivisibilityMomentBounds.divisorScore R)))
          (1 : Real) →
        LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0}
              (Erdos390.Full.FiniteProbability.expect.{0}
                (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                  (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun m => score ↑m)
                fun m => Erdos390.Full.ArithmeticModel.divInd D ↑m)
              (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S (Erdos390.Full.ArithmeticModel.divInd D))))
          (HDiv.hDiv.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta)
                (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S fun m =>
                  HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticModel.divInd D m)
                    (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m)))
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (Real.exp K)
                  (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S (Erdos390.Full.ArithmeticModel.divInd D)))
                (HMul.hMul.{0, 0, 0} beta
                  (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                    (Erdos390.Full.DivisibilityMomentBounds.divisorScore R)))))
            (HSub.hSub.{0, 0, 0} (1 : Real)
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta)
                (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                  (Erdos390.Full.DivisibilityMomentBounds.divisorScore R))))) := by sorry

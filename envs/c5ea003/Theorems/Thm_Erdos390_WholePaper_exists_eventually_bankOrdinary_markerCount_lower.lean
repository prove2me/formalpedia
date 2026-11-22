-- Prove2me | Theorems.Thm_Erdos390_WholePaper_exists_eventually_bankOrdinary_markerCount_lower
-- name    : Erdos390.WholePaper.exists_eventually_bankOrdinary_markerCount_lower
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:22:12.482613+00:00
-- url     : https://prove2.me/theorems/455cf9f4-8f30-4a64-9047-cd8c9d105a93
-- title:
--   Uniform lower bound for ordinary eligible markers
-- statement:
--   For every $c>0$ there exists $r>0$ such that, for all sufficiently large $n$ and every rational $20<Q\le y(n)$, the number $M(n,Q)$ of eligible markers for the ordinary relation between $n$ and its upper endpoint at tail parameter $c$ obeys
--   $$M(n,Q)\ge\frac{r\,s(n)}{\max\{Q,\log n\}},\qquad s(n)=\frac n{\log n}.$$
--   This converts donor occurrences into a count of distinct usable markers.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankOrdinaryDonorSupply.lean#L1241-L1341

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

theorem Erdos390.WholePaper.exists_eventually_bankOrdinary_markerCount_lower :
∀ {c : Real},
  LT.lt.{0} (0 : Real) c →
    ∃ rho,
      And (LT.lt.{0} (0 : Real) rho)
        (∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (Q : Rat),
            LT.lt.{0} (20 : Rat) Q →
              LE.le.{0} Q ↑(Erdos390.Full.ArithmeticModel.yNat n) →
                LE.le.{0}
                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} rho (Erdos390.WholePaper.secondOrderScale n))
                    (Max.max.{0} (↑Q) (Real.log ↑n)))
                  ↑(Erdos390.WholePaper.bankEligibleMarkerCount.{0, 0}
                      (Erdos390.WholePaper.bankOrdinaryEligibleRelation n
                        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) Q))) := by sorry

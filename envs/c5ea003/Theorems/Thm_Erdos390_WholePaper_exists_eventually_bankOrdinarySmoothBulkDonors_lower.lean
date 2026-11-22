-- Prove2me | Theorems.Thm_Erdos390_WholePaper_exists_eventually_bankOrdinarySmoothBulkDonors_lower
-- name    : Erdos390.WholePaper.exists_eventually_bankOrdinarySmoothBulkDonors_lower
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:07:06.332233+00:00
-- url     : https://prove2.me/theorems/ccb8033b-8308-40ef-a8f5-e590575d9353
-- title:
--   Uniform positive density of ordinary smooth bulk donors
-- statement:
--   There exists $\delta>0$ such that, for all sufficiently large natural $n$ and every rational $Q$ with $20<Q\le y(n)$, the ordinary smooth bulk donor set $D(n,Q)$ satisfies
--   $$|D(n,Q)|\ge\delta Q.$$
--   The threshold in $n$ and density are independent of $Q$, giving a uniform donor supply for the ordinary bank.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankOrdinaryDonorSupply.lean#L300-L432

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

theorem Erdos390.WholePaper.exists_eventually_bankOrdinarySmoothBulkDonors_lower :
∃ delta,
  And (LT.lt.{0} (0 : Real) delta)
    (∀ᶠ (n : Nat) in Filter.atTop.{0},
      ∀ (Q : Rat),
        LT.lt.{0} (20 : Rat) Q →
          LE.le.{0} Q ↑(Erdos390.Full.ArithmeticModel.yNat n) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} delta ↑Q)
              ↑(Finset.card.{0} (Erdos390.WholePaper.bankOrdinarySmoothBulkDonors n Q))) := by sorry

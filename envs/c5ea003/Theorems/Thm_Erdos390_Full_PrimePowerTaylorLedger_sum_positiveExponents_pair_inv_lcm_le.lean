-- Prove2me | Theorems.Thm_Erdos390_Full_PrimePowerTaylorLedger_sum_positiveExponents_pair_inv_lcm_le
-- name    : Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_pair_inv_lcm_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:30:33.667009+00:00
-- url     : https://prove2.me/theorems/805691f5-cc72-4c44-8bf2-1738483a19d1
-- title:
--   Uniform reciprocal bound for the full same-prime lcm ledger
-- statement:
--   Let $p$ be prime and $M$ a natural exponent cutoff. Let $Q=\mathrm{quadraticHalfMass}$ and $C_+=1+(4+Q)/2$, the fixed positive-prime-power lcm constant. Then
--
--   $$\sum_{k=1}^M\sum_{l=1}^M\frac1{\operatorname{lcm}(p^k,p^l)}\le\frac{C_+}{p}.$$
--
--   The complete prime-power second-moment ledger has a fixed reciprocal-prime cost independent of the moving cutoff.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperMediumNuisanceInputReduction.lean#L1814-L1928

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_pair_inv_lcm_le :
∀ {p M : Nat},
  Nat.Prime p →
    LE.le.{0}
      (∑ k ∈ Erdos390.Full.ArithmeticModel.positiveExponents M,
        ∑ l ∈ Erdos390.Full.ArithmeticModel.positiveExponents M,
          HDiv.hDiv.{0, 0, 0} (1 : Real) ↑(Nat.lcm (HPow.hPow.{0, 0, 0} p k) (HPow.hPow.{0, 0, 0} p l)))
      (HDiv.hDiv.{0, 0, 0} Erdos390.Full.PrimePowerTaylorLedger.positivePrimePowerLcmConstant ↑p) := by sorry

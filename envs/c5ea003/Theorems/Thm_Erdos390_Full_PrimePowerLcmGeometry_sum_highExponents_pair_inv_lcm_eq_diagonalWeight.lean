-- Prove2me | Theorems.Thm_Erdos390_Full_PrimePowerLcmGeometry_sum_highExponents_pair_inv_lcm_eq_diagonalWeight
-- name    : Erdos390.Full.PrimePowerLcmGeometry.sum_highExponents_pair_inv_lcm_eq_diagonalWeight
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:24:20.96106+00:00
-- url     : https://prove2.me/theorems/04e1e164-7a48-4f37-8fbb-883e9b792cdc
-- title:
--   Exact diagonal shell count for reciprocal prime-power lcms
-- statement:
--   For arbitrary natural numbers $p,A$, let $R_A=\{2,\ldots,A\}$. Then
--
--   $$\sum_{k\in R_A}\sum_{l\in R_A}\frac1{\operatorname{lcm}(p^k,p^l)}=\sum_{r\in R_A}\frac{2r-3}{p^r}.$$
--
--   The identity explains the exact diagonal weights in higher-valuation second-moment estimates.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PrimePowerLcmGeometry.lean#L30-L118

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.PrimePowerLcmGeometry.sum_highExponents_pair_inv_lcm_eq_diagonalWeight :
∀ (p A : Nat),
  Eq.{1}
    (∑ k ∈ Erdos390.Full.ArithmeticModel.highExponents A,
      ∑ l ∈ Erdos390.Full.ArithmeticModel.highExponents A,
        HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(Nat.lcm (HPow.hPow.{0, 0, 0} p k) (HPow.hPow.{0, 0, 0} p l)) : Real))
    (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents A,
      HDiv.hDiv.{0, 0, 0} (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)) : Real)
        (HPow.hPow.{0, 0, 0} (↑p : Real) r)) := by sorry

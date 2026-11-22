-- Prove2me | Theorems.Thm_Erdos390_Full_PrimePowerTaylorLedger_sum_positiveExponents_primePowerModuli_inv_lcm_le
-- name    : Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_primePowerModuli_inv_lcm_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:49:49.415325+00:00
-- url     : https://prove2.me/theorems/d530de46-199a-4515-b503-5f2249028b4f
-- title:
--   Reciprocal least-common-multiple bound for a forced prime-power row
-- statement:
--   Let $P$ be a finite set of primes, $p\in P$, and $M\in\mathbb N$. Put $\mathcal A=\{q^k:q\in P,\ 1\le k\le M\}$, and let $C_{\mathrm{pp}}$ denote the source-defined positive prime-power least-common-multiple constant. Then
--
--   $$\sum_{r=1}^{M}\sum_{a\in\mathcal A}\frac1{\operatorname{lcm}(p^r,a)}\le\frac{4\sum_{q\in P}q^{-1}+C_{\mathrm{pp}}}{p}.$$
--
--   The estimate retains the reciprocal scale of the distinguished prime when summing an entire prime-power score.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperMediumNuisanceInputReduction.lean#L2201-L2316

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

theorem Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_primePowerModuli_inv_lcm_le :
∀ (P : Finset.{0} Nat) (M p : Nat),
  Membership.mem.{0, 0} P p →
    (∀ (q : Nat), Membership.mem.{0, 0} P q → Nat.Prime q) →
      LE.le.{0}
        (∑ r ∈ Erdos390.Full.ArithmeticModel.positiveExponents M,
          ∑ a ∈ Erdos390.Full.ValuationScoreDomination.primePowerModuli P M,
            HDiv.hDiv.{0, 0, 0} (1 : Real) ↑(Nat.lcm (HPow.hPow.{0, 0, 0} p r) a))
        (HDiv.hDiv.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) (∑ q ∈ P, HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q))
            Erdos390.Full.PrimePowerTaylorLedger.positivePrimePowerLcmConstant)
          ↑p) := by sorry

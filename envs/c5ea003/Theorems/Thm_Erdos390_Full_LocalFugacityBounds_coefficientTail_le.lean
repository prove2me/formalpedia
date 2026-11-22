-- Prove2me | Theorems.Thm_Erdos390_Full_LocalFugacityBounds_coefficientTail_le
-- name    : Erdos390.Full.LocalFugacityBounds.coefficientTail_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:44:30.045193+00:00
-- url     : https://prove2.me/theorems/e7823417-335b-41a9-b2c1-80f4cbf64fa9
-- title:
--   One-prime restoration tail with logarithmic gain
-- statement:
--   Let $p,A,r$ be natural numbers with $p\ge2$. Let $B\ge0$, $L>0$, $B\le L$, and $|\eta|\le B$. For $a\ge1$ put $c_a=e^{a\eta/L}-e^{(a-1)\eta/L}$ and $T=\sum_{a=1}^A|c_a|p^{-\max(r,a)}$.
--
--   $$T\le\frac{2B}{L}e^{BA/L}\frac{r+1}{p^r}.$$
--
--   The bound preserves the factor $1/L$ uniformly in the finite exponent cutoff.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/LocalFugacityBounds.lean#L343-L460

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.LocalFugacityBounds.coefficientTail_le :
∀ {p A r : Nat} {B eta L : Real},
  LE.le.{0} (2 : Nat) p →
    LE.le.{0} (0 : Real) B →
      LT.lt.{0} (0 : Real) L →
        LE.le.{0} B L →
          LE.le.{0} (abs.{0} eta) B →
            LE.le.{0} (Erdos390.Full.LocalFugacityBounds.coefficientTail p A r eta L)
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) B) L)
                  (Real.exp (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑A) L)))
                (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real)) (HPow.hPow.{0, 0, 0} (↑p) r))) := by sorry

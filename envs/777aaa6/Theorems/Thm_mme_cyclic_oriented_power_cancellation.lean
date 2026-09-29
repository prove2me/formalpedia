-- Prove2me | Theorems.Thm_mme_cyclic_oriented_power_cancellation
-- name    : mme_cyclic_oriented_power_cancellation
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:01:36.665308+00:00
-- url     : https://prove2.me/theorems/b9535011-9acc-4ab8-bd01-ffcc8d079de3
-- title:
--   Opposite cyclic rotations cancel on oriented tensor powers
-- statement:
--   Let $T$ be an order-three tensor over a field, let $\rho$ cyclically permute its modes, and let $n\ge0$. The two opposite rotations cancel on the oriented powers:
--   $$\rho((\rho^2T)^{\otimes n})=T^{\otimes n},\qquad \rho^2((\rho T)^{\otimes n})=T^{\otimes n}.$$
--   Both conclusions are equalities of tensor objects. They identify the unfiltered half-powers arising after independent cyclic regrouping with powers of the original tensor.
-- source:
--   Naturality of tensor mode reindexing under Kronecker products and modewise linear maps.

import Theorems.Thm_mme_permutation_kronPow_eq

open MME PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_cyclic_oriented_power_cancellation {K : Type u} [Field K]
    (X : TensorObj K 3) (n : ℕ) :
    TensorObj.permObj cyclicPerm
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) X).kronPow n) =
        X.kronPow n ∧
      TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        ((TensorObj.permObj cyclicPerm X).kronPow n) = X.kronPow n := by sorry

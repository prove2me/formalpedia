-- Prove2me | Theorems.Thm_mme_toQ_kronFin
-- name    : mme_toQ_kronFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:36:24.740895+00:00
-- url     : https://prove2.me/theorems/9cb16bf2-8985-4df2-919c-9b037cdbaab4
-- title:
--   A finite ordered Kronecker product descends to a quotient product
-- statement:
--   For any finite ordered family $(T_i)_{i<n}$ of order-$d$ tensors, passing its Kronecker product to the tensor-isomorphism quotient gives the ordinary product of the quotient classes:
--
--   $$
--   \left[\bigotimes_{i<n}T_i\right]=\prod_{i<n}[T_i].
--   $$
--
--   The empty family maps to the multiplicative unit. This descent identity allows coordinatewise tensor blocks to be regrouped using commutative-semiring algebra while preserving their original ordered tensor realization.
-- source:
--   Standard compatibility of finite tensor products with the tensor-isomorphism quotient; extends TensorQ.toQ_kron from Definitions.Def_mme_rank_bridge by finite induction.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_rank_bridge
open MME BigOperators
universe u

theorem mme_toQ_kronFin
    {K : Type u} [Field K] {d n : ℕ}
    (f : Fin n → TensorObj K d) :
    TensorQ.toQ (TensorObj.kronFin n f) =
      ∏ i, TensorQ.toQ (f i) := by
  sorry

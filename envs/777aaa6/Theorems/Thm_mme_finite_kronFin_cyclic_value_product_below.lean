-- Prove2me | Theorems.Thm_mme_finite_kronFin_cyclic_value_product_below
-- name    : mme_finite_kronFin_cyclic_value_product_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:40:56.08138+00:00
-- url     : https://prove2.me/theorems/25a0eb3a-68bd-4647-841d-ce3e322b5c11
-- title:
--   Finite Kronecker products multiply cyclic tau-value lower bounds
-- statement:
--   Let $T_i$ be a finite family of order-three tensors. Suppose the cyclic symmetrization of $T_i$ has tau-value at least $b_i>0$, and choose $0\le t_i<b_i$. Then the cyclic symmetrization of their Kronecker product has tau-value at least the product of the strict targets: $$V_\tau\!\left(\operatorname{cyc}(\bigotimes_i T_i)\right)\ge\prod_i t_i.$$ This packages multiplicativity with the tensor isomorphism between the cyclic symmetrization of a finite Kronecker product and the Kronecker product of the cyclic symmetrizations.
-- source:
--   Coppersmith and Winograd, Matrix multiplication via arithmetic progressions, J. Symbolic Computation 9 (1990), symmetric-value formalism; finite multiplicativity of tau-value.

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_finite_kronFin_cyclic_value_product_below
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (tau : ℝ)
    (base target : Fin n → ℝ)
    (hbase : ∀ i, 0 < base i)
    (htarget : ∀ i, 0 ≤ target i)
    (hstrict : ∀ i, target i < base i)
    (hvalue : ∀ i,
      HasTauValueAtLeast (cyclicSymmetrization (T i)) tau (base i)) :
    HasTauValueAtLeast
      (cyclicSymmetrization (TensorObj.kronFin n T)) tau
      (∏ i, target i) := by
  sorry

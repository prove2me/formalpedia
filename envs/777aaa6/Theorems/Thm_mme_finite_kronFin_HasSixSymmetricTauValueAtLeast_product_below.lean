-- Prove2me | Theorems.Thm_mme_finite_kronFin_HasSixSymmetricTauValueAtLeast_product_below
-- name    : mme_finite_kronFin_HasSixSymmetricTauValueAtLeast_product_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:37:48.058148+00:00
-- url     : https://prove2.me/theorems/63a32b7c-f772-4643-87bc-b10308dd2fd0
-- title:
--   Six-symmetrized tau values multiply for finite Kronecker products
-- statement:
--   Let T_i be finitely many order-three tensors. Suppose each T_i has six-symmetrized tau-value at least a positive base B_i. For any nonnegative targets L_i<B_i, their finite Kronecker product has six-symmetrized tau-value at least
--
--   $$
--   \prod_i L_i.
--   $$
--
--   The result uses the full six-fold symmetrization from DWZ Definition 3.3. It supplies the product interface needed when restricted-splitting estimates are naturally coupled across cyclically permuted components: the six symmetrizations may be regrouped componentwise up to genuine tensor isomorphism, after which ordinary tau-value product closure applies.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.3 and the restricted-splitting value product in Equation (25); https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_kronFin_HasTauValueAtLeast_product_below
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_finite_kronFin_HasSixSymmetricTauValueAtLeast_product_below
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (tau : ℝ)
    (base target : Fin n → ℝ)
    (hbase : ∀ i, 0 < base i)
    (htarget : ∀ i, 0 ≤ target i)
    (hstrict : ∀ i, target i < base i)
    (hvalue : ∀ i,
      HasSixSymmetricTauValueAtLeast (T i) tau (base i)) :
    HasSixSymmetricTauValueAtLeast
      (TensorObj.kronFin n T) tau (∏ i, target i) := by
  sorry

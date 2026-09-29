-- Prove2me | Theorems.Thm_mme_finite_kronFin_HasTauValueAtLeast_product_below
-- name    : mme_finite_kronFin_HasTauValueAtLeast_product_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:23:50.741208+00:00
-- url     : https://prove2.me/theorems/476397a0-be29-448e-b3d7-032f79a4a4f3
-- title:
--   Strict local tau-value bounds multiply for a finite literal Kronecker product
-- statement:
--   Let finitely many order-three tensors have tau-value lower bounds at positive local base values. For any nonnegative local targets that are strictly below the respective bases, the literal finite Kronecker product of the tensors has tau-value at least the product of the targets. The strict slack synchronizes the finitely many local asymptotic witnesses on one positive arithmetic progression; cofinality then promotes those common-power finite extractions to an actual tau-value witness for the product tensor.
-- source:
--   Finite Kronecker-product closure of the tau-value extraction framework, used to assemble the fifteen constituent factors in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (25); https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_power_product_below
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_finite_kronFin_HasTauValueAtLeast_product_below
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (tau : ℝ)
    (base target : Fin n → ℝ)
    (hbase : ∀ i, 0 < base i)
    (htarget : ∀ i, 0 ≤ target i)
    (hstrict : ∀ i, target i < base i)
    (hvalue : ∀ i, HasTauValueAtLeast (T i) tau (base i)) :
    HasTauValueAtLeast
      (TensorObj.kronFin n T) tau (∏ i, target i) := by
  sorry

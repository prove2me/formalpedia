-- Prove2me | Theorems.Thm_mme_finite_HasTauValueAtLeast_common_power_product_below
-- name    : mme_finite_HasTauValueAtLeast_common_power_product_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:09:19.369869+00:00
-- url     : https://prove2.me/theorems/0886fd74-3655-41f1-8564-33fa015d19ff
-- title:
--   Common-power product extraction for finitely many strict tau-values
-- statement:
--   Given finitely many tensors with positive tau-value bases and nonnegative strict local targets, there is one positive integral exponent lattice on which the power of their literal Kronecker product restricts to a finite MM direct sum. At every exponent on that lattice, the total tau-weight is at least the corresponding power of the product of the local targets.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the component product in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. This theorem packages the exact common-power/product interface used by the finite component assembly.

import Mathlib.Tactic
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_multiple_below
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product

open MME BigOperators

set_option autoImplicit false

universe u

theorem mme_finite_HasTauValueAtLeast_common_power_product_below
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (tau : ℝ)
    (base target : Fin n → ℝ)
    (hbase : ∀ i, 0 < base i)
    (htarget : ∀ i, 0 ≤ target i)
    (hstrict : ∀ i, target i < base i)
    (hvalue : ∀ i, HasTauValueAtLeast (T i) tau (base i)) :
    ∃ E : ℕ, 0 < E ∧
      ∀ r : ℕ,
        ∃ (q : ℕ) (A B C : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
            ((TensorObj.kronFin n T).kronPow (r * E)) ∧
          (∏ i, target i) ^ (r * E) ≤
            ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by sorry

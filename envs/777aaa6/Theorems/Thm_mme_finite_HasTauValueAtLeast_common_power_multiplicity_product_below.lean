-- Prove2me | Theorems.Thm_mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below
-- name    : mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:09:24.791848+00:00
-- url     : https://prove2.me/theorems/99b4539e-149e-4517-8beb-c85bdd912573
-- title:
--   Multiplicity-weighted common-power product extraction
-- statement:
--   In the finite common-power product theorem, let component `i` occur with a prescribed nonnegative integral multiplicity `m_i` in one macro-product. Then one common exponent lattice supports a genuine finite MM extraction from the powered multiplicity-weighted tensor product, with total tau-weight at least the corresponding power of the weighted product of local targets. Zero multiplicities are allowed.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the integral Table-2 occurrence product in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. This is the multiplicity-aware synchronization rule needed after clearing profile denominators.

import Mathlib.Tactic
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_multiple_below
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product

open MME BigOperators

set_option autoImplicit false

universe u

theorem mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (multiplicity : Fin n → ℕ) (tau : ℝ)
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
            ((TensorObj.kronFin n
              (fun i ↦ (T i).kronPow (multiplicity i))).kronPow (r * E)) ∧
          (∏ i, (target i) ^ (multiplicity i)) ^ (r * E) ≤
            ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by sorry

-- Prove2me | solution 1 for mme_finite_kronFin_cyclic_value_product_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:42:59.361338+00:00
-- url     : https://prove2.me/submissions/e71ef769-505c-4e0b-adc4-57ad720fa563

import Mathlib.Tactic
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_kronFin_HasTauValueAtLeast_product_below
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem cyclicSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i ↦ cyclicSymmetrization (T i)))
      (cyclicSymmetrization (TensorObj.kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, cyclicSymmetrization_eq_public_perm,
    ← TensorQ.toQ_mul, ← TensorQ.permAut_toQ, map_prod]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

theorem solution
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
  have hproduct := mme_finite_kronFin_HasTauValueAtLeast_product_below
    (fun i ↦ cyclicSymmetrization (T i)) tau base target
      hbase htarget hstrict hvalue
  exact mme_HasTauValueAtLeast_mono_restrict
    (cyclicSymmetrization_kronFin_isomorphic T).1 hproduct

-- Prove2me | solution 1 for mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:18:49.084316+00:00
-- url     : https://prove2.me/submissions/44cac6d3-7fec-41a2-9826-c57aa4809169

import Mathlib.Tactic
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
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

private theorem cyclicSymmetrization_kronFin_kronPow_isomorphic
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (multiplicity : Fin n → ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i ↦
        (cyclicSymmetrization (T i)).kronPow (multiplicity i)))
      (cyclicSymmetrization
        (TensorObj.kronFin n (fun i ↦
          (T i).kronPow (multiplicity i)))) := by
  have hfactor : TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i ↦
        (cyclicSymmetrization (T i)).kronPow (multiplicity i)))
      (TensorObj.kronFin n (fun i ↦
        cyclicSymmetrization ((T i).kronPow (multiplicity i)))) := by
    rw [← TensorQ.toQ_eq_iff]
    simp only [mme_toQ_kronFin]
    apply Finset.prod_congr rfl
    intro i _hi
    exact TensorQ.toQ_eq_iff.mpr
      (mme_cyclicSymmetrization_kronPow_isomorphic
        (T i) (multiplicity i))
  exact hfactor.trans
    (cyclicSymmetrization_kronFin_isomorphic
      (fun i ↦ (T i).kronPow (multiplicity i)))

theorem solution
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (multiplicity : Fin n → ℕ)
    (tau : ℝ) (endpoint : Fin n → ℝ)
    (hendpoint : ∀ i, 0 < endpoint i)
    (hlocal : ∀ (i : Fin n) (V : ℝ),
      0 ≤ V → V < endpoint i →
      HasTauValueAtLeast (cyclicSymmetrization (T i)) tau V) :
    ∀ W : ℝ, 0 ≤ W →
      W < ∏ i, (endpoint i) ^ (multiplicity i) →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (TensorObj.kronFin n
            (fun i ↦ (T i).kronPow (multiplicity i)))) tau W := by
  intro W hW hWstrict
  have hproduct :=
    mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
      (fun i ↦ cyclicSymmetrization (T i)) multiplicity tau endpoint
      hendpoint hlocal W hW hWstrict
  exact mme_HasTauValueAtLeast_mono_restrict
    (cyclicSymmetrization_kronFin_kronPow_isomorphic T multiplicity).1
    hproduct

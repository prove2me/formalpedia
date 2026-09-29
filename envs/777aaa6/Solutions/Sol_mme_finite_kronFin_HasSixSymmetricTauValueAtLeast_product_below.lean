-- Prove2me | solution 1 for mme_finite_kronFin_HasSixSymmetricTauValueAtLeast_product_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:40:34.219413+00:00
-- url     : https://prove2.me/submissions/92f9a201-50ef-41f0-80cb-08ea983760d5

import Mathlib.Tactic
import Definitions.Def_mme_six_symmetrized_tau_value
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
  apply (TensorQ.toQ_eq_iff).1
  rw [mme_toQ_kronFin]
  rw [cyclicSymmetrization_eq_public_perm]
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
  rw [← TensorQ.permAut_toQ, ← TensorQ.permAut_toQ]
  simp_rw [mme_toQ_kronFin]
  rw [map_prod, map_prod]
  simp_rw [cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.permAut_toQ]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

private theorem sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i ↦ sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [mme_toQ_kronFin]
  change
    ∏ i, TensorQ.toQ (sixSymmetrization (T i)) =
      TensorQ.toQ
        (TensorObj.kron
          (cyclicSymmetrization (TensorObj.kronFin n T))
          (TensorObj.permObj swapFirstTwoPerm
            (cyclicSymmetrization (TensorObj.kronFin n T))))
  rw [TensorQ.toQ_kron]
  have hcyclicQ := (TensorQ.toQ_eq_iff).2
    (cyclicSymmetrization_kronFin_isomorphic T)
  rw [← hcyclicQ]
  rw [← TensorQ.permAut_toQ]
  rw [← hcyclicQ]
  simp_rw [mme_toQ_kronFin]
  change
    ∏ i, TensorQ.toQ (sixSymmetrization (T i)) =
      (∏ i, TensorQ.toQ (cyclicSymmetrization (T i))) *
        TensorQ.permAut swapFirstTwoPerm
          (∏ i, TensorQ.toQ (cyclicSymmetrization (T i)))
  rw [map_prod, ← Finset.prod_mul_distrib]
  simp_rw [show ∀ i, sixSymmetrization (T i) =
      TensorObj.kron (cyclicSymmetrization (T i))
        (TensorObj.permObj swapFirstTwoPerm
          (cyclicSymmetrization (T i))) from fun _ ↦ rfl,
    TensorQ.toQ_kron, TensorQ.permAut_toQ]

theorem solution
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
  have hbase6 : ∀ i, 0 < (base i) ^ (6 : ℕ) := fun i ↦
    pow_pos (hbase i) 6
  have htarget6 : ∀ i, 0 ≤ (target i) ^ (6 : ℕ) := fun i ↦
    pow_nonneg (htarget i) 6
  have hstrict6 : ∀ i,
      (target i) ^ (6 : ℕ) < (base i) ^ (6 : ℕ) := by
    intro i
    exact pow_lt_pow_left₀ (hstrict i) (htarget i) (by norm_num)
  have hproduct :
      HasTauValueAtLeast
        (TensorObj.kronFin n (fun i ↦ sixSymmetrization (T i)))
        tau (∏ i, (target i) ^ (6 : ℕ)) :=
    mme_finite_kronFin_HasTauValueAtLeast_product_below
      (fun i ↦ sixSymmetrization (T i)) tau
      (fun i ↦ (base i) ^ (6 : ℕ))
      (fun i ↦ (target i) ^ (6 : ℕ))
      hbase6 htarget6 hstrict6 hvalue
  have htransport :
      HasTauValueAtLeast (sixSymmetrization (TensorObj.kronFin n T))
        tau (∏ i, (target i) ^ (6 : ℕ)) :=
    mme_HasTauValueAtLeast_mono_restrict
      (sixSymmetrization_kronFin_isomorphic T).1 hproduct
  change HasTauValueAtLeast (sixSymmetrization (TensorObj.kronFin n T))
    tau ((∏ i, target i) ^ (6 : ℕ))
  simpa only [Finset.prod_pow] using htransport

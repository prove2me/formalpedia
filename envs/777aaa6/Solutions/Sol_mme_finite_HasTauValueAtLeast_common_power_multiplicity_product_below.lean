-- Prove2me | solution 1 for mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:10:12.316591+00:00
-- url     : https://prove2.me/submissions/8b78c8eb-fff9-49e5-86f4-2067c1ff40da

import Mathlib.Tactic
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_multiple_below
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

universe u

private theorem kronFin_weighted_kronPow_isomorphic_for_tau_product
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d) (multiplicity : Fin n → ℕ) (N : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n
        (fun i ↦ (T i).kronPow (N * multiplicity i)))
      ((TensorObj.kronFin n
        (fun i ↦ (T i).kronPow (multiplicity i))).kronPow N) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, TensorQ.toQ_kronPow, mme_toQ_kronFin]
  simp_rw [TensorQ.toQ_kronPow]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul, Nat.mul_comm N (multiplicity i)]

theorem solution
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
            ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨E, hE, hcommon⟩ :=
    mme_finite_HasTauValueAtLeast_common_multiple_below
      T tau base target hbase htarget hstrict hvalue
  refine ⟨E, hE, ?_⟩
  intro r
  let N := r * E
  have hlocal : ∀ i : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          ((T i).kronPow (N * multiplicity i)) ∧
        (target i) ^ (N * multiplicity i) ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    intro i
    have h := hcommon (r * multiplicity i) i
    have hexponent : (r * multiplicity i) * E = N * multiplicity i := by
      dsimp [N]
      ac_rfl
    simpa only [hexponent] using h
  obtain ⟨q, A, B, C, hrestrict, hweight⟩ :=
    mme_finite_MM_extractions_kronFin_tau_product
      (fun i ↦ (T i).kronPow (N * multiplicity i)) tau
      (fun i ↦ (target i) ^ (N * multiplicity i))
      (fun i ↦ pow_nonneg (htarget i) _) hlocal
  refine ⟨q, A, B, C, ?_, ?_⟩
  · exact TensorObj.Restrict.trans hrestrict
      (kronFin_weighted_kronPow_isomorphic_for_tau_product
        T multiplicity N).1
  · calc
      (∏ i, (target i) ^ (multiplicity i)) ^ (r * E) =
          ∏ i, ((target i) ^ (multiplicity i)) ^ N := by
        rw [show r * E = N from rfl]
        exact (Finset.prod_pow Finset.univ N
          (fun i ↦ (target i) ^ (multiplicity i))).symm
      _ = ∏ i, (target i) ^ (N * multiplicity i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [← pow_mul, Nat.mul_comm (multiplicity i) N]
      _ ≤ ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := hweight


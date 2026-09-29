-- Prove2me | solution 1 for mme_MMObj_tau_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:40:50.622113+00:00
-- url     : https://prove2.me/submissions/04d1f448-2807-4046-b3fa-398ce2a746d1

import Mathlib.Tactic
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_kronFin_MMObj_iso

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem kronFin_const_eq_kronPow
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) :
    ∀ n : ℕ, TensorObj.kronFin n (fun _ ↦ T) = T.kronPow n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change TensorObj.kron T
          (TensorObj.kronFin n (fun _ ↦ T)) =
        TensorObj.kron T (T.kronPow n)
      rw [ih]

theorem solution
    {K : Type u} [Field K]
    (n m p : ℕ) (tau : ℝ) :
    HasTauValueAtLeast (MMObj K n m p) tau
      (((n * m * p : ℕ) : ℝ) ^ tau) := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
  intro epsilon hepsilon
  apply Frequently.of_forall
  intro N
  let a : Fin 1 → ℕ := fun _ ↦ n ^ N
  let b : Fin 1 → ℕ := fun _ ↦ m ^ N
  let c : Fin 1 → ℕ := fun _ ↦ p ^ N
  refine ⟨1, a, b, c, ?_, ?_⟩
  · change TensorObj.Restrict
      (MMObj K (n ^ N) (m ^ N) (p ^ N))
      ((MMObj K n m p).kronPow N)
    have hiso := mme_kronFin_MMObj_iso
      (K := K) N (fun _ ↦ n) (fun _ ↦ m) (fun _ ↦ p)
    rw [kronFin_const_eq_kronPow] at hiso
    simpa using hiso.2
  · change
      (((n * m * p : ℕ) : ℝ) ^ tau) ^ N * (1 - epsilon) ≤
        ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)
    simp only [Fin.sum_univ_one, a, b, c]
    have hbase : 0 ≤ (((n * m * p : ℕ) : ℝ)) := Nat.cast_nonneg _
    have hpow :
        (((n * m * p : ℕ) : ℝ) ^ tau) ^ N =
          (((n ^ N * m ^ N * p ^ N : ℕ) : ℝ) ^ tau) := by
      rw [Real.rpow_pow_comm hbase]
      congr 1
      push_cast
      ring
    rw [← hpow]
    have hnonneg : 0 ≤ (((n * m * p : ℕ) : ℝ) ^ tau) ^ N := by
      positivity
    nlinarith

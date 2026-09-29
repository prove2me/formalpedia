-- Prove2me | solution 1 for mme_finite_HasTauValueAtLeast_common_multiple_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:05:27.128796+00:00
-- url     : https://prove2.me/submissions/0ed597f8-562c-48d3-a18a-adcbddfd77bc

import Mathlib.Tactic
import Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below

open BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (tau : ℝ)
    (base target : Fin n → ℝ)
    (hbase : ∀ i, 0 < base i)
    (htarget : ∀ i, 0 ≤ target i)
    (hstrict : ∀ i, target i < base i)
    (hvalue : ∀ i, HasTauValueAtLeast (T i) tau (base i)) :
    ∃ E : ℕ, 0 < E ∧
      ∀ (r : ℕ) (i : Fin n),
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
            ((T i).kronPow (r * E)) ∧
          (target i) ^ (r * E) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  classical
  have hlocal : ∀ i : Fin n,
      ∃ e : ℕ, 0 < e ∧
        ∀ r : ℕ,
          ∃ (k : ℕ) (a b c : Fin k → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
              ((T i).kronPow (r * e)) ∧
            (target i) ^ (r * e) ≤
              ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := fun i ↦
    mme_HasTauValueAtLeast_multiple_extractions_below
      (T i) tau (base i) (target i)
      (hbase i) (htarget i) (hstrict i) (hvalue i)
  choose e he using hlocal
  let E := ∏ i, e i
  have hE : 0 < E := by
    apply Finset.prod_pos
    intro i hi
    exact (he i).1
  refine ⟨E, hE, ?_⟩
  intro r i
  have hdiv : e i ∣ E := by
    exact Finset.dvd_prod_of_mem e (Finset.mem_univ i)
  obtain ⟨s, hs⟩ := hdiv
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := (he i).2 (r * s)
  have hexponent : (r * s) * e i = r * E := by
    rw [hs]
    ac_rfl
  refine ⟨k, a, b, c, ?_, ?_⟩
  · simpa only [hexponent] using hrestrict
  · simpa only [hexponent] using hweight


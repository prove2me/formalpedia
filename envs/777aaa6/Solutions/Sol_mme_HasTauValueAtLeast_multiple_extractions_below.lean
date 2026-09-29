-- Prove2me | solution 1 for mme_HasTauValueAtLeast_multiple_extractions_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:57:17.126079+00:00
-- url     : https://prove2.me/submissions/7d44e904-d4b0-47c9-b2cf-685768a50c4c

import Mathlib.Tactic
import Theorems.Thm_mme_kronPow_kronPow_isomorphic
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_bigAdd_MM_kronPow_tau_flatten
import Theorems.Thm_mme_HasTauValueAtLeast_exists_positive_extraction_below

open BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ)
    (hB : 0 < B) (hV : 0 ≤ V) (hVB : V < B)
    (h : HasTauValueAtLeast T tau B) :
    ∃ e : ℕ, 0 < e ∧
      ∀ r : ℕ,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            (T.kronPow (r * e)) ∧
          V ^ (r * e) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨e, he, k, a, b, c, hrestrict, hweight⟩ :=
    mme_HasTauValueAtLeast_exists_positive_extraction_below
      T tau B V hB hV hVB h
  refine ⟨e, he, ?_⟩
  intro r
  obtain ⟨q, A, B', C, hflatten, hweightPower⟩ :=
    mme_bigAdd_MM_kronPow_tau_flatten (K := K) a b c tau (r := r)
  refine ⟨q, A, B', C, ?_, ?_⟩
  · exact TensorObj.Restrict.trans hflatten
      (TensorObj.Restrict.trans
        (mme_restrict_kronPow hrestrict r)
        (mme_kronPow_kronPow_isomorphic T e r).1)
  · calc
      V ^ (r * e) = (V ^ e) ^ r := by
        rw [Nat.mul_comm, pow_mul]
      _ ≤ (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r :=
        pow_le_pow_left₀ (pow_nonneg hV e) hweight r
      _ = ∑ j, (((A j * B' j * C j : ℕ) : ℝ) ^ tau) :=
        hweightPower.symm


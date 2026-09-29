-- Prove2me | solution 1 for mme_MM_word_tau_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:45:09.811573+00:00
-- url     : https://prove2.me/submissions/06f1e8af-9016-4a0e-9f0d-664fb0719d0c

import Mathlib.Tactic

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {k r : ℕ} (a b c : Fin k → ℕ) (tau : ℝ) :
    (∑ p : Fin r → Fin k,
        ((((∏ t, a (p t)) * (∏ t, b (p t)) * (∏ t, c (p t)) : ℕ) : ℝ) ^ tau)) =
      (∑ i : Fin k, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r := by
  calc
    (∑ p : Fin r → Fin k,
        ((((∏ t, a (p t)) * (∏ t, b (p t)) * (∏ t, c (p t)) : ℕ) : ℝ) ^ tau)) =
        ∑ p : Fin r → Fin k,
          ∏ t, (((a (p t) * b (p t) * c (p t) : ℕ) : ℝ) ^ tau) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hprod :
          (∏ t, a (p t)) * (∏ t, b (p t)) * (∏ t, c (p t)) =
            ∏ t, a (p t) * b (p t) * c (p t) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      rw [hprod, Nat.cast_prod]
      exact (Real.finset_prod_rpow Finset.univ
        (fun t ↦ ((a (p t) * b (p t) * c (p t) : ℕ) : ℝ))
        (fun t ht ↦ Nat.cast_nonneg _) tau).symm
    _ = (∑ i : Fin k, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r :=
      (Fintype.sum_pow
        (fun i : Fin k ↦ (((a i * b i * c i : ℕ) : ℝ) ^ tau)) r).symm


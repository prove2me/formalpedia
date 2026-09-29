-- Prove2me | solution 1 for RecursiveMixedRadix.splitting_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:47:57.311698+00:00
-- url     : https://prove2.me/submissions/df48578d-3cc6-492a-888e-ee51f526909b

-- Sol generated from NumberTheory/RecursiveMixedRadix.lean
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix
import Theorems.Thm_RecursiveMixedRadix_value_lt
import Theorems.Thm_RecursiveMixedRadix_weight_succ

/-!
# Recursive mixed-radix representations

This file isolates the general mixed-radix mechanism behind factoradics and
recursive-base systems.  A radix sequence `r` determines place values
`weight r 0 = 1` and `weight r (k+1) = r k * weight r k`.

The main results prove, constructively and without cardinality arguments, that
valid length-`k` digit strings represent exactly the naturals below
`weight r k`, and do so uniquely.
-/

open RecursiveMixedRadix

open Finset





@[simp] theorem weight_zero (r : ℕ → ℕ) : weight r 0 = 1 := by rfl



theorem value_succ (r c : ℕ → ℕ) (k : ℕ) :
    value r c (k + 1) = value r c k + c k * weight r k := by
  simp [value, Finset.sum_range_succ]

theorem Valid.of_succ {r c : ℕ → ℕ} {k : ℕ} (h : Valid r c (k + 1)) :
    Valid r c k := fun i hi => h i (Nat.lt_succ_of_lt hi)









open RecursiveMixedRadix in
theorem solution{r c : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
    (hc : Valid r c (k + 1)) :
    value r c (k + 1) / weight r k = c k := by
  rw [value_succ]
  have hval : value r c k < weight r k := value_lt hr (fun i hi => hc i (Nat.lt_succ_of_lt hi))
  have hpos : 0 < weight r k := by
    exact Nat.rec (by simp [weight_zero])
      (fun m ihm => by simp [weight_succ, Nat.mul_pos (hr m) ihm]) k
  calc
    (value r c k + c k * weight r k) / weight r k =
        (value r c k + weight r k * c k) / weight r k := by rw [Nat.mul_comm]
    _ = value r c k / weight r k + c k := Nat.add_mul_div_left _ _ hpos
    _ = 0 + c k := by rw [Nat.div_eq_of_lt hval]
    _ = c k := by omega

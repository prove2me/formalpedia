-- Prove2me | solution 1 for RecursiveMixedRadix.value_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:46:29.688718+00:00
-- url     : https://prove2.me/submissions/8a99ed88-5937-473f-ad5d-fad56f3b8b67

-- Sol generated from NumberTheory/RecursiveMixedRadix.lean
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix
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


@[simp] theorem value_zero (r c : ℕ → ℕ) : value r c 0 = 0 := by
  simp [value]

theorem value_succ (r c : ℕ → ℕ) (k : ℕ) :
    value r c (k + 1) = value r c k + c k * weight r k := by
  simp [value, Finset.sum_range_succ]

theorem Valid.of_succ {r c : ℕ → ℕ} {k : ℕ} (h : Valid r c (k + 1)) :
    Valid r c k := fun i hi => h i (Nat.lt_succ_of_lt hi)









open RecursiveMixedRadix in
theorem solution{r c : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
    (hc : Valid r c k) : value r c k < weight r k := by
  induction k with
  | zero => simp [value_zero, weight_zero]
  | succ k ih =>
    have hck : c k < r k := hc k (Nat.lt_succ_self k)
    rw [value_succ, weight_succ]
    have hpos : 0 < weight r k := by
      exact Nat.rec (by simp [weight_zero]) (fun m ihm => by simp [weight_succ, Nat.mul_pos (hr m) ihm]) k
    have h1 : value r c k < weight r k := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have h2 : r k ≥ 1 := hr k
    have h3 : weight r k ≥ 1 := hpos
    have h4 : value r c k ≤ weight r k - 1 := Nat.le_sub_one_of_lt h1
    have h5 : c k ≤ r k - 1 := Nat.le_sub_one_of_lt hck
    have h6 : c k * weight r k ≤ (r k - 1) * weight r k := Nat.mul_le_mul_right _ h5
    have h7 : (weight r k - 1) + (r k - 1) * weight r k = r k * weight r k - 1 := by
      have hmul : (r k - 1) * weight r k = r k * weight r k - weight r k := by
        rw [tsub_mul, one_mul]
      rw [hmul]
      have hle : weight r k ≤ r k * weight r k := by nlinarith
      omega
    have h8 : c k * weight r k < r k * weight r k := (Nat.mul_lt_mul_right hpos).mpr hck
    calc value r c k + c k * weight r k ≤ (weight r k - 1) + (r k - 1) * weight r k := Nat.add_le_add h4 h6
      _ = r k * weight r k - 1 := h7
      _ < r k * weight r k := Nat.sub_lt (by positivity) (by norm_num)

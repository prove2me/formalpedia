-- Prove2me | solution 1 for RecursiveMixedRadix.digit_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:40:42.817095+00:00
-- url     : https://prove2.me/submissions/82efbd41-883d-4ec5-8bcd-aaca8e29da3f

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










open RecursiveMixedRadix in
theorem solution{r : ℕ → ℕ} (n k : ℕ) :
    n = value r (digit r n) k + (n / weight r k) * weight r k := by
  induction k with
  | zero => simp [value_zero, weight_zero]
  | succ k ih =>
    rw [value_succ, weight_succ]
    have div_eq : n / weight r k / r k = n / (r k * weight r k) := by
      rw [Nat.mul_comm]
      exact Nat.div_div_eq_div_mul n (weight r k) (r k)
    rw [← div_eq]
    have da := Nat.div_add_mod (n / weight r k) (r k)
    have digit_eq : digit r n k = n / weight r k % r k := rfl
    have key : n / weight r k * weight r k = digit r n k * weight r k + n / (r k * weight r k) * (r k * weight r k) := by
      calc n / weight r k * weight r k
          = (r k * (n / weight r k / r k) + n / weight r k % r k) * weight r k := by rw [da]
        _ = r k * (n / weight r k / r k) * weight r k + n / weight r k % r k * weight r k := by ring
        _ = n / weight r k / r k * (r k * weight r k) + digit r n k * weight r k := by rw [digit_eq]; ring
        _ = n / (r k * weight r k) * (r k * weight r k) + digit r n k * weight r k := by rw [← div_eq]
        _ = digit r n k * weight r k + n / (r k * weight r k) * (r k * weight r k) := by ring
    calc n
        = value r (digit r n) k + n / weight r k * weight r k := ih
      _ = value r (digit r n) k + (digit r n k * weight r k + n / (r k * weight r k) * (r k * weight r k)) := by rw [key]
      _ = value r (digit r n) k + digit r n k * weight r k + n / (r k * weight r k) * (r k * weight r k) := by ring
      _ = value r (digit r n) k + digit r n k * weight r k + n / weight r k / r k * (r k * weight r k) := by rw [← div_eq]

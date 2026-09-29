-- Prove2me | solution 1 for Negabinary.exists_canonical
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:26:13.199022+00:00
-- url     : https://prove2.me/submissions/3d7d0ca8-ca45-4da8-8eb3-48dc76256a52

-- Sol generated from Applications/AlienNumberSystems/Negabinary.lean
import Mathlib
import Definitions.Def_Applications_AlienNumberSystems_Negabinary

/-!
# Negabinary: unique finite representations of all integers

This file proves that evaluation in radix `-2` gives a bijection between canonical
finite bit strings and the integers. Digits are stored least-significant first.
-/

open Negabinary








@[simp] theorem canonical_nil : Canonical [] := by
  simp [Canonical]


/-- The chosen digit is exactly the Euclidean residue modulo two. -/
theorem digit_eq_emod (z : ℤ) : digit z = z % 2 := by
  unfold digit bit
  have : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rcases this with h | h <;> simp [h]

/-- Removing the chosen digit leaves an even integer. -/
theorem two_dvd_sub_digit (z : ℤ) : 2 ∣ z - digit z := by
  rw [digit_eq_emod]
  omega

/-- One negabinary division step reconstructs the original integer. -/
theorem reconstruct (z : ℤ) : digit z - 2 * next z = z := by
  simp [next]
  have h : 2 * ((z - digit z) / 2) = z - digit z := by
    exact Int.mul_ediv_cancel' (two_dvd_sub_digit z)
  linarith

/-- Except at zero and the one exceptional point `-1`, one negabinary division
step strictly decreases absolute value. (Indeed `next (-1) = 1`.) -/
theorem natAbs_next_lt (z : ℤ) (hz : z ≠ 0) (hneg : z ≠ -1) :
    (next z).natAbs < z.natAbs := by
  have hrec := reconstruct z
  rw [digit_eq_emod] at hrec
  omega








/-- Computational witnesses for small positive and negative integers. -/
example : value [true, true, false, true] = (-9 : ℤ) := by norm_num [value]
example : value [false, true, true] = (2 : ℤ) := by norm_num [value]
example : value [true, true, true, false, true] = (19 : ℤ) := by norm_num [value]


open Negabinary in
theorem solution(z : ℤ) :
    ∃ l : List Bool, Canonical l ∧ value l = z := by
  by_cases hz : z = 0
  · exact ⟨[], canonical_nil, hz.symm⟩
  · -- z ≠ 0: use strong induction on natAbs z
    have aux : ∀ m : ℕ, ∀ w : ℤ, w.natAbs = m → ¬w = 0 → ∃ l, Canonical l ∧ value l = w := fun m =>
      Nat.strongRecOn m fun n ih w hw hw0 => by
        by_cases hneg : w = -1
        · -- Case w = -1: bit (-1) = true, next (-1) = 1
          refine ⟨[true, true], ?_, ?_⟩
          · simp [Canonical]
          · -- value [true, true] = 1 - 2*1 = -1
            norm_num [value]
            rw [hneg.symm]
        · -- Case w ≠ -1: natAbs (next w) < natAbs w
          have hlt : (next w).natAbs < n := by rw [← hw]; exact natAbs_next_lt w hw0 hneg
          by_cases hnext : next w = 0
          · -- next w = 0 means w = 1, so bit w = true
            refine ⟨[true], ?_, ?_⟩
            · simp [Canonical]
            · simp [value]
              have hw1 : w = 1 := by
                have hrecon := reconstruct w
                simp [hnext] at hrecon
                have : digit w = 0 ∨ digit w = 1 := by
                  unfold digit bit
                  split <;> simp
                cases this with
                | inl h => exact (hw0 (hrecon.symm.trans h)).elim
                | inr h => exact hrecon.symm.trans h
              rw [hw1]
          · -- next w ≠ 0: use IH
            obtain ⟨l, hcan, hv⟩ := ih (next w).natAbs hlt (next w) rfl hnext
            refine ⟨bit w :: l, ?_, ?_⟩
            · -- Show bit w :: l is canonical
              cases l with
              | nil => simp [value] at hv; exact absurd hv.symm hnext
              | cons x xs =>
                simp [Canonical] at hcan ⊢
                exact hcan
            · -- Show value (bit w :: l) = w
              simp [value, hv]
              have : (if bit w = true then (1 : ℤ) else 0) = digit w := by
                unfold digit bit
                split <;> simp
              rw [this]
              exact reconstruct w
    exact aux _ _ rfl hz

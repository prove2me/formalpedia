-- Prove2me | solution 1 for Negabinary.value_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:27:30.025669+00:00
-- url     : https://prove2.me/submissions/352df833-49f8-40ca-b522-17302e39c2ba

-- Sol generated from Applications/AlienNumberSystems/Negabinary.lean
import Mathlib
import Definitions.Def_Applications_AlienNumberSystems_Negabinary
import Theorems.Thm_Negabinary_canonical_value_eq_zero

/-!
# Negabinary: unique finite representations of all integers

This file proves that evaluation in radix `-2` gives a bijection between canonical
finite bit strings and the integers. Digits are stored least-significant first.
-/

open Negabinary








@[simp] theorem canonical_nil : Canonical [] := by
  simp [Canonical]

theorem canonical_tail {b : Bool} {bs : List Bool} (h : Canonical (b :: bs)) :
    Canonical bs := by
  cases bs with
  | nil => exact canonical_nil
  | cons c cs =>
    simp [Canonical] at h ⊢
    exact h





/-- The parity of a represented integer recovers its first bit. -/
theorem value_cons_emod (b : Bool) (bs : List Bool) :
    value (b :: bs) % 2 = if b then 1 else 0 := by
  simp [value]
  cases b <;> rfl







/-- Computational witnesses for small positive and negative integers. -/
example : value [true, true, false, true] = (-9 : ℤ) := by norm_num [value]
example : value [false, true, true] = (2 : ℤ) := by norm_num [value]
example : value [true, true, true, false, true] = (19 : ℤ) := by norm_num [value]


open Negabinary in
theorem solution{l₁ l₂ : List Bool} (h₁ : Canonical l₁)
    (h₂ : Canonical l₂) (hv : value l₁ = value l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact (canonical_value_eq_zero h₂ hv.symm).symm
  | cons b₁ bs₁ ih =>
    cases l₂ with
    | nil => cases canonical_value_eq_zero h₁ hv
    | cons b₂ bs₂ =>
      have hb : b₁ = b₂ := by
        have h1 := value_cons_emod b₁ bs₁
        have h2 := value_cons_emod b₂ bs₂
        rw [hv] at h1
        have h3 : (if b₁ then (1 : ℤ) else 0) = (if b₂ then (1 : ℤ) else 0) := by
          rw [← h2, ← h1]
        cases b₁ <;> cases b₂ <;> simp_all
      have hc1 : Canonical bs₁ := canonical_tail h₁
      have hc2 : Canonical bs₂ := canonical_tail h₂
      have hv' : value bs₁ = value bs₂ := by
        simp [value] at hv
        simp [hb] at hv
        omega
      have htails : bs₁ = bs₂ := ih hc1 hc2 hv'
      rw [hb, htails]

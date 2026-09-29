-- Prove2me | solution 1 for Negabinary.canonical_value_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:26:12.647662+00:00
-- url     : https://prove2.me/submissions/afd6ebbb-8724-4ba9-905c-5e5e3bb9030f

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

theorem canonical_tail {b : Bool} {bs : List Bool} (h : Canonical (b :: bs)) :
    Canonical bs := by
  cases bs with
  | nil => exact canonical_nil
  | cons c cs =>
    simp [Canonical] at h ⊢
    exact h












/-- Computational witnesses for small positive and negative integers. -/
example : value [true, true, false, true] = (-9 : ℤ) := by norm_num [value]
example : value [false, true, true] = (2 : ℤ) := by norm_num [value]
example : value [true, true, true, false, true] = (19 : ℤ) := by norm_num [value]


open Negabinary in
theorem solution{l : List Bool} (hc : Canonical l)
    (hv : value l = 0) : l = [] := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp [value] at hv
    cases b with
    | true =>
      simp at hv
      omega
    | false =>
      simp at hv
      have hcan : Canonical bs := canonical_tail hc
      have hbs : bs = [] := ih hcan hv
      simp [hbs, Canonical] at hc

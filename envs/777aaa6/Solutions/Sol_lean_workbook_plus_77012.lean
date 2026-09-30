-- Prove2me | solution 1 for lean_workbook_plus_77012
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:28:53.170689+00:00
-- url     : https://prove2.me/submissions/049f996b-fd2c-4767-9264-ec10a9d99755

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) :
    (∀ x y, f (x + x * f y) = x + y * f (f x)) ↔ ∀ x, f x = x := by
  constructor
  · intro h
    have hzero : f 0 = 0 := by simpa using h 0 0
    have hone : f 1 = 1 := by simpa [hzero] using h 1 0
    have hshift (y : ℝ) : f (1 + f y) = 1 + y := by simpa [hone] using h 1 y
    have hinj : Function.Injective f := by
      intro a b hab
      have ha := hshift a
      have hb := hshift b
      rw [hab] at ha
      linarith
    have hneg : f (-1) = -1 := by
      have heq : f (1 + f (-1)) = f 0 := by rw [hshift, hzero]; norm_num
      have heq' := hinj heq
      linarith
    have hinvol (x : ℝ) : f (f x) = x := by
      have hx := h x (-1)
      simp only [hneg, mul_neg_one, add_neg_cancel, hzero, neg_one_mul] at hx
      linarith
    have hdouble (x : ℝ) : f (2 * x) = 2 * x := by
      simpa only [hone, hinvol, mul_one, one_mul, two_mul] using h x 1
    intro x
    have heq : (2 : ℝ) * (x / 2) = x := by ring
    simpa only [heq] using hdouble (x / 2)
  · intro h x y
    simp only [h]
    ring

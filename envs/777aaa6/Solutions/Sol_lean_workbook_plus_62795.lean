-- Prove2me | solution 1 for lean_workbook_plus_62795
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:55.918676+00:00
-- url     : https://prove2.me/submissions/d837cd02-352c-462b-baa4-2fdc244e8214

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem quadratic_classification (f : ℤ → ℤ)
    (hf1 : ∀ x y, f (x + y) = f x + f y + 6 * x * y + 1)
    (hf2 : ∀ x, f x = f (-x)) (x : ℤ) : f x = 3 * x ^ 2 - 1 := by
  have h0 := hf1 0 0
  norm_num at h0
  have hx := hf1 x (-x)
  simp only [add_neg_cancel] at hx
  nlinarith [hf2 x]

theorem quadratic_model :
    (∀ x y : ℤ, 3 * (x + y) ^ 2 - 1 =
      (3 * x ^ 2 - 1) + (3 * y ^ 2 - 1) + 6 * x * y + 1) ∧
    (∀ x : ℤ, 3 * x ^ 2 - 1 = 3 * (-x) ^ 2 - 1) := by
  constructor <;> intros <;> ring

theorem solution (f : ℤ → ℤ)
    (hf1 : ∀ x y, f (x + y) = f x + f y + 6 * x * y + 1)
    (hf2 : ∀ x, f x = f (-x)) : f 3 = 26 := by
  simpa using quadratic_classification f hf1 hf2 3

#print axioms solution
#print axioms quadratic_classification

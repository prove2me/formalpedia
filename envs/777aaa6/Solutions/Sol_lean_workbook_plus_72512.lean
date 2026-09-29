-- Prove2me | solution 1 for lean_workbook_plus_72512
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:58:57.098717+00:00
-- url     : https://prove2.me/submissions/088e3a66-5689-4f57-a54b-8ce7cd3cbd76

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + b + c = 12)
    (h2 : a * b + b * c + c * a = 45) : 50 ≤ a * b * c ∧ a * b * c ≤ 54 := by
  have hd : 0 ≤ (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - c))) (sq_nonneg (b - c))
  have hid : (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 =
      (a + b + c) ^ 2 * (a * b + b * c + c * a) ^ 2
      - 4 * (a * b + b * c + c * a) ^ 3
      - 4 * (a + b + c) ^ 3 * (a * b * c)
      - 27 * (a * b * c) ^ 2
      + 18 * (a + b + c) * (a * b + b * c + c * a) * (a * b * c) := by ring
  rw [h1, h2] at hid
  constructor <;> nlinarith only [hd, hid, sq_nonneg (a * b * c - 50), sq_nonneg (a * b * c - 54)]

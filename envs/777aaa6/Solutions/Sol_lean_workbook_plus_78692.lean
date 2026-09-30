-- Prove2me | solution 1 for lean_workbook_plus_78692
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:39:47.784531+00:00
-- url     : https://prove2.me/submissions/f3ece05f-174d-4d8c-86b9-261be207986b

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (hf: f = fun n => n * f 1 - n + 1) : ∀ n : ℕ, f n = n * f 1 - n + 1 := by
  intro n
  exact congrFun hf n

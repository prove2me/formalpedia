-- Prove2me | solution 1 for lean_workbook_plus_34755
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:11.604486+00:00
-- url     : https://prove2.me/submissions/1b2938d9-12dd-46d5-8c0e-1358af7b5d17

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : 1 ≤ a ∧ a ≤ 3) (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => if x = 1 then a else 2 * x + |x - 1| / (x - 1)) : (∀ x, if x = 1 then f x = a else f x = 2 * x + |x - 1| / (x - 1)) := by
  (intros; simp_all)

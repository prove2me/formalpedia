-- Prove2me | solution 1 for lean_workbook_plus_56319
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:44.837598+00:00
-- url     : https://prove2.me/submissions/acf3708c-80df-4892-9e94-99902652bc79

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => 2 - x) : ∀ x, f x = 2 - x := by
  (intros; simp_all)

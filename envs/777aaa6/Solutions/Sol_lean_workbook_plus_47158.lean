-- Prove2me | solution 1 for lean_workbook_plus_47158
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:42.730781+00:00
-- url     : https://prove2.me/submissions/a20c9546-4008-4188-ac94-be739296466a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℚ → ℚ) (hf: f = fun x => x) : ∀ x, f x = x := by
  (intros; simp_all)

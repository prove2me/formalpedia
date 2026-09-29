-- Prove2me | solution 1 for lean_workbook_plus_26300
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:19.997192+00:00
-- url     : https://prove2.me/submissions/608cb7ec-573b-42b6-b3b1-988d319eb77a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (hf: f = fun x => x^2) : ∀ x, f x = x^2 := by
  (intros; simp_all)

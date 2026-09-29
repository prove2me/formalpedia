-- Prove2me | solution 1 for lean_workbook_plus_44889
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:53.939266+00:00
-- url     : https://prove2.me/submissions/82489bdf-2745-4859-b49b-b90df13f5de2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (k : ℝ) : (fun x => k * f x) = k • f := by
  rfl

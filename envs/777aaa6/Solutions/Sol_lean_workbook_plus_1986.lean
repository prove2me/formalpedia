-- Prove2me | solution 1 for lean_workbook_plus_1986
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:40.548968+00:00
-- url     : https://prove2.me/submissions/0788af17-fa45-48a2-bdc2-2128c2c96f51

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x ≤ -5 ∨ 3 ≤ x) ↔ x ∈ Set.Iic (-5) ∪ Set.Ici 3 := by
  norm_num

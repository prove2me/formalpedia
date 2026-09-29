-- Prove2me | solution 1 for lean_workbook_plus_19361
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:05.429974+00:00
-- url     : https://prove2.me/submissions/4e834576-f959-4041-9941-4f917d503aa5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : (a^3 * b^3 + b^3 * c^3 + c^3 * a^3 + 3 * a^2 * b^2 * c^2)^2 ≥ 0 := by
  (intros; positivity)

-- Prove2me | solution 1 for lean_workbook_plus_11742
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:39.587655+00:00
-- url     : https://prove2.me/submissions/8041f84c-9afd-471a-bb72-23a32f50eb73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r : ℝ)
  (h₀ : (r + 1)^2 - (r + 1) + 1 = 0.7 * ((r + 2)^2 - 3)) :
  r^2 - 6 * r + 1 = 0 := by
  (intros; linarith)

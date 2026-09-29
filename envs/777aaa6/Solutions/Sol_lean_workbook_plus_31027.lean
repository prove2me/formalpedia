-- Prove2me | solution 1 for lean_workbook_plus_31027
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:10.071705+00:00
-- url     : https://prove2.me/submissions/e68d53ec-a2ce-4391-b219-b45115f3edc1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {f : ℝ → ℝ} (c : ℝ) (h : 3 * f 0 + 3 * c = 0) : f 0 = -c := by
  (intros; linarith)

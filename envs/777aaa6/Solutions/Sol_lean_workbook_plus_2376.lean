-- Prove2me | solution 1 for lean_workbook_plus_2376
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:42.991437+00:00
-- url     : https://prove2.me/submissions/4cdb0c3d-7978-428c-9b54-d9388780759d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x d r t : ℝ) : d = r * t ∧ d = 15 * (3 - x) ∧ d = 3 * x → x = 2.5 := by
  (intros; linarith)

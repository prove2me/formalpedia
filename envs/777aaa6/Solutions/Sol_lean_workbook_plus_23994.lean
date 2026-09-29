-- Prove2me | solution 1 for lean_workbook_plus_23994
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:57.507857+00:00
-- url     : https://prove2.me/submissions/919b7d4d-77d0-4862-807b-783f1be77ffe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f g : ℝ → ℝ) (hf : f = fun x => g (1 / (2 * x + 1))) : f = fun x => g (1 / (2 * x + 1)) := by
  (intros; simp_all)

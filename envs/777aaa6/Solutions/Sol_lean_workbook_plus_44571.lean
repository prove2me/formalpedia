-- Prove2me | solution 1 for lean_workbook_plus_44571
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:08:51.264698+00:00
-- url     : https://prove2.me/submissions/36fa0baa-f985-43a4-ab7c-66e5835df847

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ (f : ℝ → ℝ), (∀ x y :ℝ, abs (f x - f y) > 1)) := by
  intro h
  have := h (fun _ => 0) 0 0
  norm_num at this

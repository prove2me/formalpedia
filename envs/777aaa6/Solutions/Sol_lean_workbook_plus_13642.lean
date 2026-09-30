-- Prove2me | solution 1 for lean_workbook_plus_13642
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:54.640589+00:00
-- url     : https://prove2.me/submissions/dc7ab5ea-2c92-4bbe-a9a7-705f67217304

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f = fun (t : ℝ) => t - 1/2) : ∀ t ∈ Set.Ico (0 : ℝ) 1, f t = t - 1/2 := by
  intro t _
  rw [hf]

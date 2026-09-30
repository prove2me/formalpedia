-- Prove2me | solution 1 for lean_workbook_plus_29209
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:20.904641+00:00
-- url     : https://prove2.me/submissions/05d84b1c-eb56-441d-8cd5-c1e979221266

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f x > 1 / Real.sqrt x): ∃ x, f x > 1 / Real.sqrt x :=
  ⟨x, hf⟩

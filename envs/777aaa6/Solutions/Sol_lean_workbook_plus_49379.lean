-- Prove2me | solution 1 for lean_workbook_plus_49379
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:39.283974+00:00
-- url     : https://prove2.me/submissions/242ecd55-e530-49c7-bf5b-b42a96109e42

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f g : ℝ → ℝ) (x : ℝ) (hf : f = fun (x:ℝ) => (6 - x)^(1 / 2)) (hg : g = fun (x:ℝ) => (3 - x)^(1 / 2)) : (f x - f 2) / (g x - g 2) = (f x - f 2) / (x - 2) * (x - 2) / (g x - g 2) := by
  (intros; simp_all)

-- Prove2me | Theorems.Thm_lean_workbook_plus_64939
-- name    : lean_workbook_plus_64939
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/004e1114-3b7e-4ae5-a510-f4ff07a9f057
-- statement:
--   The equation when $ y$ is the watch time and $ x$ is the real time is $ y = 60x - (2x + \frac {24}{60}x) = \frac {288x}{5}$ with x in hours and y in minutes. Thus we have to find the time when $ y = 600$ . This gives $ x = 125/12$ or $ 10: 25$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64939  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : y = 60 * x - (2 * x + 24 / 60 * x))
  (h₂ : y = 600) :
  x = 125 / 12   :=  by sorry

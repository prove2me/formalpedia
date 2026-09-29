-- Prove2me | Theorems.Thm_lean_workbook_plus_61644
-- name    : lean_workbook_plus_61644
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ff7b6503-badd-414d-8170-a86a96871d69
-- statement:
--   Let the bat's cost be $y,$ and let the ball's cost be $x.$ We know $y = x + 100$ (in cents), so substituting, we have $x+100+x=110,$ so $x=5$ cents and $y = 105$ cents. The ball costs $5$ cents.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61644  (x y : ℝ)
  (h₀ : y = x + 100)
  (h₁ : x + y = 110) :
  x = 5 ∧ y = 105   :=  by sorry

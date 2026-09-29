-- Prove2me | Theorems.Thm_lean_workbook_plus_60547
-- name    : lean_workbook_plus_60547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/385c080f-9c0f-4171-a1b3-cf7d57947ba2
-- statement:
--   Call the 2 numbers x and y. Add three to both so $x+3+y+3$ . Then multiply each number by two so $2x+6+2y+6$ . Group it so it will be $2x+2y+12$ and factor out the 2. $2(x+y)+12$ . Since $x+y=S$ , plug it in so $2s+12$ and it will be E.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60547  (x y s : ℝ)
  (h₀ : x + y = s)
  (h₁ : 2 * x + 2 * y + 12 = 2 * s + 12) :
  2 * x + 2 * y + 12 = 2 * (x + y) + 12   :=  by sorry

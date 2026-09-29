-- Prove2me | Theorems.Thm_lean_workbook_plus_82259
-- name    : lean_workbook_plus_82259
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/dc4062a6-1d57-45a1-990a-da195a1b57e3
-- statement:
--   He worked by himself for $2$ hours and $3$ people worked for $1.5$ hours. Since they all work at the same rate, it would have taken him $3*1.5=4.5$ hours to finish what they did together by himself. If you add the $2$ hours, you could say it takes $6.5$ “work-hours” to complete the job, or $390$ “work-minutes”. The next day they finish in $174$ minutes. On tuesday, if you call how much time the painter works by himself $x$ , then you can set up the equation $x+\frac{390-x}{3}=174$ . Solving, you get $x=66$ . So, the answer is $66$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82259  (x : ℝ)
  (h₀ : x + (390 - x) / 3 = 174) :
  x = 66   :=  by sorry

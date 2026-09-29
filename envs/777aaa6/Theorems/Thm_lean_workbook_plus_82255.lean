-- Prove2me | Theorems.Thm_lean_workbook_plus_82255
-- name    : lean_workbook_plus_82255
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/11c3de67-2c22-42b9-b96f-d848f1860b27
-- statement:
--   Prove that if $f(x) = e^{cx}$, then $f(x)f(y) = f(x+y)$ for all real x and y.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82255 (x y : ℝ) (c : ℝ) : exp (c * x) * exp (c * y) = exp (c * (x + y))   :=  by sorry

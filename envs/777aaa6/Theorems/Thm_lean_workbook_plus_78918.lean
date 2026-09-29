-- Prove2me | Theorems.Thm_lean_workbook_plus_78918
-- name    : lean_workbook_plus_78918
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/27b24de8-1c45-41cd-837d-73a2314a5134
-- statement:
--   By Cauchy-Schwartz, $\frac {1}{x+y}+\frac {1}{x+z}\ge \frac{4}{2x+y+z} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78918 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : (1 / (x + y) + 1 / (x + z)) ≥ 4 / (2 * x + y + z)   :=  by sorry

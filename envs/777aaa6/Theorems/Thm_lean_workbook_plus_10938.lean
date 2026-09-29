-- Prove2me | Theorems.Thm_lean_workbook_plus_10938
-- name    : lean_workbook_plus_10938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/11b5af2c-2384-4bed-89af-9bd142a0ae48
-- statement:
--   Prove that $ a^2 + b^2 + c^2 - ab - bc - ca = \frac {1}{2}((a - b)^2 + (a - c)^2 + (b - c)^2) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10938 (a b c : ℝ) : a^2 + b^2 + c^2 - (a * b + b * c + c * a) = 1 / 2 * ((a - b)^2 + (a - c)^2 + (b - c)^2)   :=  by sorry

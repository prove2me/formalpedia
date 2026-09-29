-- Prove2me | Theorems.Thm_lean_workbook_plus_37687
-- name    : lean_workbook_plus_37687
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4b9271b2-a7c8-44c3-9508-a85d9dadb2d5
-- statement:
--   The cost of $3$ hamburgers, $5$ milk shakes, and $1$ order of fries at a certain fast food restaurant is $\$23.50$ . At the same restaurant, the cost of $5$ hamburgers, $9$ milk shakes, and $1$ order of fries is $\$39.50$ . What is the cost of $2$ hamburgers, $2$ milk shakes and $2$ orders of fries at this restaurant?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37687 (h m f : ℝ) : 3 * h + 5 * m + 1 * f = 23.50 ∧ 5 * h + 9 * m + 1 * f = 39.50 → 2 * h + 2 * m + 2 * f = 15   :=  by sorry

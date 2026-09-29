-- Prove2me | Theorems.Thm_lean_workbook_plus_80102
-- name    : lean_workbook_plus_80102
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a8dfd397-12db-4cc0-8e07-aebcf04ce52e
-- statement:
--   $5^3>8^2$ $\implies$ $5^{\frac 32}>8$ $\implies$ $\frac 32>\log_5 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80102 : 5 ^ (3 / 2) > 8 → 3 / 2 > Real.logb 5 8   :=  by sorry

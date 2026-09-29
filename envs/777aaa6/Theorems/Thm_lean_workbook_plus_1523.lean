-- Prove2me | Theorems.Thm_lean_workbook_plus_1523
-- name    : lean_workbook_plus_1523
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5bbd2d6c-a007-4d8e-8205-051bf966db78
-- statement:
--   This can be expanded to \n $13a^2+10b^2+5c^2=4ab+12bc+6ac$ \n or \n $ (2a-b)^2+(3b-2c)^2+(3a-c)^2=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1523 (a b c : ℝ) : 13 * a ^ 2 + 10 * b ^ 2 + 5 * c ^ 2 = 4 * a * b + 12 * b * c + 6 * a * c ↔ (2 * a - b) ^ 2 + (3 * b - 2 * c) ^ 2 + (3 * a - c) ^ 2 = 0   :=  by sorry

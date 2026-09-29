-- Prove2me | Theorems.Thm_lean_workbook_plus_61706
-- name    : lean_workbook_plus_61706
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/16490fec-ed5e-4397-aca5-b52a6eb2d0b5
-- statement:
--   Prove that the inequality is equivalent to:\n$3 (a^3+ b^3 + c^3+ 6 a b c - 3 a^2 c - 3 c^2 b - 3 b^2 a )^2\ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61706 : 3 * (a^3 + b^3 + c^3 + 6 * a * b * c - 3 * a^2 * c - 3 * c^2 * b - 3 * b^2 * a)^2 ≥ 0   :=  by sorry

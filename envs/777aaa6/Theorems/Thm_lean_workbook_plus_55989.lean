-- Prove2me | Theorems.Thm_lean_workbook_plus_55989
-- name    : lean_workbook_plus_55989
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/9ad15c23-5776-4132-8086-0fa3273df822
-- statement:
--   $\sum_{cyc}a^4c^2\geq \sum_{cyc}ab^2c^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55989 (a b c : ℝ) : a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2 ≥ a * b ^ 2 * c ^ 3 + b * c ^ 2 * a ^ 3 + c * a ^ 2 * b ^ 3   :=  by sorry

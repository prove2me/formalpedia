-- Prove2me | Theorems.Thm_lean_workbook_plus_67660
-- name    : lean_workbook_plus_67660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/14076e89-24c4-4314-b8ca-dc576074099a
-- statement:
--   Simplify the expression: $\frac{2013^3 - 2\cdot 2013^2\cdot 2014 + 3\cdot 2013\cdot 2014^2 - 2014^3 + 1}{2013\cdot 2014}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67660 (a b : ℤ) (ha : a = 2013) (hb : b = 2014) : (a^3 - 2 * a^2 * b + 3 * a * b^2 - b^3 + 1) / (a * b) = 2013   :=  by sorry

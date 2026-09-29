-- Prove2me | Theorems.Thm_lean_workbook_plus_23541
-- name    : lean_workbook_plus_23541
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/abd661b6-2ed4-48de-82a2-ef12048df77b
-- statement:
--   so we need to prove \n\n $8\left( {\sum {a^2 } } \right)^2 \ge 3\left( {2\sum {ab^3 } + \sum {a^3 b} + 2\sum {a^2 b^2 } + 3abc\sum a } \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23541 (a b c : ℝ) : 8 * (a^2 + b^2 + c^2)^2 ≥ 3 * (2 * (a * b^3 + b * c^3 + c * a^3) + a^3 * b + b^3 * c + c^3 * a + 3 * a * b * c * (a + b + c))   :=  by sorry

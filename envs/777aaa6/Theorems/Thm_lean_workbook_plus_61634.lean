-- Prove2me | Theorems.Thm_lean_workbook_plus_61634
-- name    : lean_workbook_plus_61634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/78c3c57a-d1ae-4709-9180-57383c0c482b
-- statement:
--   Prove that \((x^4 + x^2 y^2) + (y^4 + y^2 z^2) + (z^4 + z^2 x^2) \geq 2(x^3 y + y^3 z + z^3 x)\) using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61634 (x y z : ℝ) : (x^4 + x^2 * y^2) + (y^4 + y^2 * z^2) + (z^4 + z^2 * x^2) ≥ 2 * (x^3 * y + y^3 * z + z^3 * x)   :=  by sorry

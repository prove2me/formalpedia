-- Prove2me | Theorems.Thm_lean_workbook_plus_9587
-- name    : lean_workbook_plus_9587
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/af069082-1297-4276-ac29-6d3249f46bc4
-- statement:
--   Given $f(x,y,z) = xy$, prove that $V = x^4y^2z^2 - x^3y^3z^2 - y^3z^3x^2 + y^2z^4x^2 + x^2y^4z^2 - x^3y^2z^3 \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9587 (x y z : ℝ) : x ^ 4 * y ^ 2 * z ^ 2 - x ^ 3 * y ^ 3 * z ^ 2 - y ^ 3 * z ^ 3 * x ^ 2 + y ^ 2 * z ^ 4 * x ^ 2 + x ^ 2 * y ^ 4 * z ^ 2 - x ^ 3 * y ^ 2 * z ^ 3 ≥ 0   :=  by sorry

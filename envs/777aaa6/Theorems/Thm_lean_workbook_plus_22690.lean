-- Prove2me | Theorems.Thm_lean_workbook_plus_22690
-- name    : lean_workbook_plus_22690
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6d06a24c-b8c3-4950-b17e-420dbc928394
-- statement:
--   Prove that \(\left( {a^2 + b^2 + c^2 } \right)^2 - 3\left( {a^3 b + b^3 c + c^3 a} \right) = \frac{1}{2}\sum\limits_{}^{} {\left( {a^2 - b^2 + 2bc - ab - ac} \right)} ^2\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22690 (a b c : ℝ) :
  (a^2 + b^2 + c^2)^2 - 3 * (a^3 * b + b^3 * c + c^3 * a) =
    1 / 2 * ((a^2 - b^2 + 2 * b * c - a * b - a * c)^2 +
      (b^2 - c^2 + 2 * c * a - b * c - b * a)^2 +
      (c^2 - a^2 + 2 * a * b - c * a - c * b)^2)   :=  by sorry

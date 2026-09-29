-- Prove2me | Theorems.Thm_lean_workbook_plus_38165
-- name    : lean_workbook_plus_38165
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/516d9117-37c3-495a-8863-d1acf1afae12
-- statement:
--   $\Longleftrightarrow a^4+b^4+c^4\geq \frac{1}{2}(ab(a^2+b^2)+bc(b^2+c^2)+ca(c^2+a^2))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38165 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ 1 / 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2))   :=  by sorry

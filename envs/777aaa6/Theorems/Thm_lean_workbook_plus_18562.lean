-- Prove2me | Theorems.Thm_lean_workbook_plus_18562
-- name    : lean_workbook_plus_18562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d070fd11-f782-481b-a277-86b9633a78f7
-- statement:
--   Prove that $(b^2+d^2)x^2-2(ab+cd)xy+(a^2+c^2)y^2\geq0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18562 (a b c d x y : ℝ) : (b^2 + d^2) * x^2 - 2 * (a * b + c * d) * x * y + (a^2 + c^2) * y^2 ≥ 0   :=  by sorry

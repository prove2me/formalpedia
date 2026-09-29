-- Prove2me | Theorems.Thm_lean_workbook_plus_65798
-- name    : lean_workbook_plus_65798
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/fc34e9f3-d94e-4598-a661-b35c1c17aee9
-- statement:
--   $\sqrt{a^2+ab+b^2}+\sqrt{b^2+bc+c^2}=\sqrt{3\left( \frac{a+b}{2}\right)^2+\left( \frac{a-b}{2}\right)^2}+\sqrt{3\left( \frac{b+c}{2}\right)^2+\left( \frac{b-c}{2}\right)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65798 (a b c : ℝ) : Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) = Real.sqrt (3 * (a + b) ^ 2 / 4 + (a - b) ^ 2 / 4) + Real.sqrt (3 * (b + c) ^ 2 / 4 + (b - c) ^ 2 / 4)   :=  by sorry

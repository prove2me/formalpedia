-- Prove2me | Theorems.Thm_lean_workbook_plus_79794
-- name    : lean_workbook_plus_79794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/33705345-4ebb-439e-ad0f-8b0833bf2953
-- statement:
--   After homogeneous,the inequality becomes \n $(a^2+b^2+c^2)^3-(a^3+b^3+c^3-abc)^2=\frac{1}{2}\sum{(a^2+b^2)(ab+bc+ca-c^2)^2}+\frac{3}{2}\sum{a^2b^2(a^2+b^2)}+2a^2b^2c^2\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79794 :  ∀ a b c : ℝ, (a^2 + b^2 + c^2)^3 - (a^3 + b^3 + c^3 - a * b * c)^2 = (1 / 2) * (a^2 + b^2) * (a * b + b * c + c * a - c^2)^2 + (1 / 2) * (b^2 + c^2) * (b * c + c * a + a * b - a^2)^2 + (1 / 2) * (c^2 + a^2) * (c * a + a * b + b * c - b^2)^2 + (3 / 2) * a^2 * b^2 * (a^2 + b^2) + (3 / 2) * b^2 * c^2 * (b^2 + c^2) + (3 / 2) * c^2 * a^2 * (c^2 + a^2) + 2 * a^2 * b^2 * c^2   :=  by sorry

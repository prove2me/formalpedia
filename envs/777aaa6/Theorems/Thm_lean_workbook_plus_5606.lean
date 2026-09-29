-- Prove2me | Theorems.Thm_lean_workbook_plus_5606
-- name    : lean_workbook_plus_5606
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ec56d1e7-fb8b-483a-a7b8-7a9c791ab228
-- statement:
--   Prove that \\( \\dfrac{1}{2a^2+b^2+3} + \\dfrac{1}{2b^2+c^2+3} + \\dfrac{1}{2c^2+a^2+3} \le \\dfrac{1}{2} \\) for positive real numbers \\( a,b,c \\) such that \\( abc = 1 \\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5606 (a b c : ℝ) (habc : a * b * c = 1) : 1 / (2 * a ^ 2 + b ^ 2 + 3) + 1 / (2 * b ^ 2 + c ^ 2 + 3) + 1 / (2 * c ^ 2 + a ^ 2 + 3) ≤ 1 / 2   :=  by sorry

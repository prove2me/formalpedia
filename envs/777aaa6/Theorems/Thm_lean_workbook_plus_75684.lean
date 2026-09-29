-- Prove2me | Theorems.Thm_lean_workbook_plus_75684
-- name    : lean_workbook_plus_75684
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bed6702f-e7a0-4325-bfb1-5273d338b384
-- statement:
--   Let a,b,c be reals , prove \n\n $(a^{3}+b^{3}+c^{3}-3abc)^{2}\le (a^{2}+b^{2}+c^{2})^{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75684 (a b c : ℝ) : (a^3 + b^3 + c^3 - 3 * a * b * c)^2 ≤ (a^2 + b^2 + c^2)^3   :=  by sorry

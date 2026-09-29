-- Prove2me | Theorems.Thm_lean_workbook_plus_7691
-- name    : lean_workbook_plus_7691
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/feb55bf6-75b8-4d13-871e-6c34cdf1abe0
-- statement:
--   Prove that $a^3+b^3+c^3-3abc=(a+b+c)(a^2+b^2+c^2-ab-ac-bc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7691 : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2 - a*b - a*c - b*c)   :=  by sorry

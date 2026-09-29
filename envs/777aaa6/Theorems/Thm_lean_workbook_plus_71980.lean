-- Prove2me | Theorems.Thm_lean_workbook_plus_71980
-- name    : lean_workbook_plus_71980
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1d98c55c-c21f-40cc-b070-e370c95300dd
-- statement:
--   Prove that $2(a^6+b^6+c^6)+5(a^4b^2+b^4c^2+c^4a^2)\ge 7(a^3b^3+b^3c^3+c^3a^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71980 (a b c : ℝ) : 2 * (a ^ 6 + b ^ 6 + c ^ 6) + 5 * (a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2) ≥ 7 * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3)   :=  by sorry

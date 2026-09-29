-- Prove2me | Theorems.Thm_lean_workbook_plus_55103
-- name    : lean_workbook_plus_55103
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2b8025fd-8377-4f93-b616-c1d62e135e14
-- statement:
--   If $a,b,c$ are negative numbers, and $a+b+c=3,$ prove that $2(a^2+b^2+c^2+9)(a^3b+b^3c+c^3a+3abc)\leq9(a^2+b^2+c^2+abc)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55103 (a b c : ℝ) (ha : a < 0) (hb : b < 0) (hc : c < 0) (habc : a + b + c = 3) : 2 * (a ^ 2 + b ^ 2 + c ^ 2 + 9) * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + 3 * a * b * c) ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b * c) ^ 2   :=  by sorry

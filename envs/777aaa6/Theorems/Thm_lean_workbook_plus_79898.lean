-- Prove2me | Theorems.Thm_lean_workbook_plus_79898
-- name    : lean_workbook_plus_79898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/07273aa4-bd23-4845-8568-ddd200404742
-- statement:
--   prove that $ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c)\le{3abc}$\n\na,b,c - triangle side lengths.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79898 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b + c - a) + b^2 * (a + c - b) + c^2 * (a + b - c) ≤ 3 * a * b * c   :=  by sorry

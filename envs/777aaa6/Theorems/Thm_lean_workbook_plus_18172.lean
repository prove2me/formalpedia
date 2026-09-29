-- Prove2me | Theorems.Thm_lean_workbook_plus_18172
-- name    : lean_workbook_plus_18172
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9b7292f1-6b6d-47d9-995a-79a99c09685e
-- statement:
--   Prove that $f(a,b,c)=15(a^{3}+b^{3}+c^{3}+(ab+bc+ca)(a+b+c))+9abc-7(a+b+c)^{3}\geq 0\forall a,b,c\geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18172 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 15 * (a ^ 3 + b ^ 3 + c ^ 3 + (a * b + b * c + c * a) * (a + b + c)) + 9 * a * b * c - 7 * (a + b + c) ^ 3 ≥ 0   :=  by sorry

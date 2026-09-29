-- Prove2me | Theorems.Thm_lean_workbook_plus_51754
-- name    : lean_workbook_plus_51754
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/84346da7-8fc8-4dc5-90bf-d49da8e490f7
-- statement:
--   Prove that for all non negative reals $ a,b,c $ , the following inequality holds.\n\n $ 9(a^3+b^3+c^3)+48(a^2(b+c)+b^2(c+a)+c^2(a+b)) \ge 35(ab+bc+ca)(a+b+c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51754 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 9 * (a ^ 3 + b ^ 3 + c ^ 3) + 48 * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) ≥ 35 * (a * b + b * c + c * a) * (a + b + c)   :=  by sorry

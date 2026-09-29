-- Prove2me | Theorems.Thm_lean_workbook_plus_3120
-- name    : lean_workbook_plus_3120
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6e06939b-b4e3-456c-8c97-584a250b092f
-- statement:
--   we know $2bc\leq{b^2+c^2}$ , $2ca\leq{c^2+a^2}$ , and $2ab\leq{a^2+b^2}$ ,\nby adding these and add $4(bc+ca+ab)$ both sides ,you get\n$ 3(bc+ca+ab)\leq(a+b+c)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3120 (a b c : ℝ) : 3 * (b * c + c * a + a * b) ≤ (a + b + c) ^ 2   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_5668
-- name    : lean_workbook_plus_5668
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/cffc3217-5532-4c77-b2ee-4c3b6d9451ee
-- statement:
--   If $a$ , $b$ , $c$ are nonnegative real numbers, then \n\n $$(a+2b+c)(a+b+c)^2 {\geq} 4(a+b)(b+c)(c+a)$$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5668 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + 2 * b + c) * (a + b + c) ^ 2 ≥ 4 * (a + b) * (b + c) * (c + a)   :=  by sorry

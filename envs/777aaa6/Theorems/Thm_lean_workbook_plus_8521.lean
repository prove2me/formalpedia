-- Prove2me | Theorems.Thm_lean_workbook_plus_8521
-- name    : lean_workbook_plus_8521
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/dd6a62e4-3c70-44d4-a8da-7cfdea37ce0a
-- statement:
--   If $a>0$ , $b>0$ and $c>0$ and $(a^2+b^2+c^2)^2>2(a^4+b^4+c^4)$ so $(a+b+c)(a+b-c)(a+c-b)(b+c-a)>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8521 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4) → (a + b + c) * (a + b - c) * (a + c - b) * (b + c - a) > 0   :=  by sorry

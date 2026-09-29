-- Prove2me | Theorems.Thm_lean_workbook_plus_31306
-- name    : lean_workbook_plus_31306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/37ebb794-e4fb-4b75-b1d3-cf53f9b99010
-- statement:
--   Show that for any positive real numbers $a,b,c$ the following inequality is true: \n $$4(a^3+b^3+c^3+3)\geq 3(a+1)(b+1)(c+1)$$ When does equality hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31306 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3) ≥ 3 * (a + 1) * (b + 1) * (c + 1)   :=  by sorry

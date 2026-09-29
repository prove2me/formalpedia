-- Prove2me | Theorems.Thm_lean_workbook_plus_28930
-- name    : lean_workbook_plus_28930
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/a9e72145-4cf2-4b76-917b-7ba338d1f818
-- statement:
--   If $,a,b,c>0$ . prove that: $2(a+b+c)(a^2 + b^2 + c^2)>=a^3 + b^3 + c^3 + 15abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28930 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a ^ 3 + b ^ 3 + c ^ 3 + 15 * a * b * c   :=  by sorry

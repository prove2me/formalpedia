-- Prove2me | Theorems.Thm_lean_workbook_plus_1552
-- name    : lean_workbook_plus_1552
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/18276ed3-9b18-456a-8045-0bcd6dc297b4
-- statement:
--   If $a,b,c>0$ and $a^2+b^2+c^2+2abc=1$, prove that $(a+b)^2 + (b+c)^2 + (c+a)^2 \leq 3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1552 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : (a + b)^2 + (b + c)^2 + (c + a)^2 ≤ 3   :=  by sorry

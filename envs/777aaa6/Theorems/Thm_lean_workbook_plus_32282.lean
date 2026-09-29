-- Prove2me | Theorems.Thm_lean_workbook_plus_32282
-- name    : lean_workbook_plus_32282
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c7fa5c6f-28fc-4f8c-a8b4-db84278ca5d3
-- statement:
--   Let $a,b,c>0$ and $abc=1.$ Prove that $$a+b^2+c\le a^2+b^3+c^2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32282 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a + b^2 + c ≤ a^2 + b^3 + c^2   :=  by sorry

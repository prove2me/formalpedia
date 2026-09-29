-- Prove2me | Theorems.Thm_lean_workbook_plus_11835
-- name    : lean_workbook_plus_11835
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/805bf5c7-3ae8-49b5-ac91-f56a980983ef
-- statement:
--   Let $a,b,c > 0$ and $\frac{1}{a+1}+\frac{1}{b+1}+\frac{1}{c+1}=2$ . $$abc\le\frac{1}{8}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11835 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1) = 2 → a * b * c ≤ 1 / 8)   :=  by sorry

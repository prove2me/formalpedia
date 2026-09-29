-- Prove2me | Theorems.Thm_lean_workbook_plus_62248
-- name    : lean_workbook_plus_62248
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cea1d396-92e4-43ca-87dc-dcfc5887354c
-- statement:
--   Let $a,b,c>0$ and $\frac{a}{1+b}+\frac{b}{1+c}+\frac{c}{1+a}=\frac{3}{2}$ . Prove that $abc\leq1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62248 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a / (1 + b) + b / (1 + c) + c / (1 + a)) = 3 / 2) : a * b * c ≤ 1   :=  by sorry

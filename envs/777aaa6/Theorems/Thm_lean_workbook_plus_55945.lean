-- Prove2me | Theorems.Thm_lean_workbook_plus_55945
-- name    : lean_workbook_plus_55945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/85f573e0-6280-4851-bd54-b2acd2afaf07
-- statement:
--   Let $a,b,c$ be positive real numbers such that $\frac{3}{a+3}+\frac{2}{b+2}+\frac{1}{c+1}=\frac{9}{4}$ .Prove that $ \frac{1}{a}+\frac{1}{b}+\frac{1}{c}\geq 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55945 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : 3 / (a + 3) + 2 / (b + 2) + 1 / (c + 1) = 9 / 4 → 1 / a + 1 / b + 1 / c ≥ 1   :=  by sorry

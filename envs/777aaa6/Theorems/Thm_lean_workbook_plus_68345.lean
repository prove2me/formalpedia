-- Prove2me | Theorems.Thm_lean_workbook_plus_68345
-- name    : lean_workbook_plus_68345
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ae7c43bb-0807-43b7-bd1e-d433da930a3e
-- statement:
--   Let $a, b, c>0 $ and $\frac {1}{a}+\frac {1}{b}+\frac {1}{c}+\frac {1}{a+1}+\frac {1}{b+1}+\frac {1}{c+1}=\frac 92$ . Prove that $$ abc\geq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68345 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (1 / a + 1 / b + 1 / c + 1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1)) = 9 / 2) : a * b * c ≥ 1   :=  by sorry

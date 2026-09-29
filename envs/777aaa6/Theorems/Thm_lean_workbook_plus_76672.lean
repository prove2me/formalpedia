-- Prove2me | Theorems.Thm_lean_workbook_plus_76672
-- name    : lean_workbook_plus_76672
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e60726c4-b1b0-4384-8360-d329d396f1db
-- statement:
--   If $a,b,c>0\;,$ Then prove that $\frac{2}{a+b}+\frac{2}{b+c}+\frac{2}{c+a}\geq \frac{9}{a+b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76672 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ≥ 9 / (a + b + c)   :=  by sorry

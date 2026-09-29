-- Prove2me | Theorems.Thm_lean_workbook_plus_1215
-- name    : lean_workbook_plus_1215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ac7cae99-9a84-46e1-be23-e11a1aa133d9
-- statement:
--   Prove that $(c+d)(\frac{1}{a+d}+\frac{1}{b+c}) \ge \frac{4(c+d)}{a+b+c+d}$ given $a,b,c,d>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1215 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (c + d) * (1 / (a + d) + 1 / (b + c)) ≥ 4 * (c + d) / (a + b + c + d)   :=  by sorry

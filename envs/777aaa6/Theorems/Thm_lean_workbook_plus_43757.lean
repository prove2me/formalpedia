-- Prove2me | Theorems.Thm_lean_workbook_plus_43757
-- name    : lean_workbook_plus_43757
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/3dc19867-3edb-423b-a4c7-a8e07ec3fd2a
-- statement:
--   Prove that $(a+b)(\frac{1}{b+d}+\frac{1}{a+c}) \ge \frac{4(a+b)}{a+b+c+d}$ given $a,b,c,d>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43757 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b) * (1 / (b + d) + 1 / (a + c)) ≥ 4 * (a + b) / (a + b + c + d)   :=  by sorry

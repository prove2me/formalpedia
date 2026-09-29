-- Prove2me | Theorems.Thm_lean_workbook_plus_81851
-- name    : lean_workbook_plus_81851
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/ff47fce9-6c88-44e4-b84c-06e320dd5613
-- statement:
--   For a,b,c>0.Prove that \n $\frac{{{{(a + b + c)}^2}}}{{ab + bc + ca}} \ge \frac{{a + b}}{{a + c}} + \frac{{b + c}}{{b + a}} + \frac{{c + a}}{{c + b}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81851 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 2 / (a * b + b * c + c * a) ≥ (a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b)   :=  by sorry

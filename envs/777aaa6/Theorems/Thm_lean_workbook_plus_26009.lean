-- Prove2me | Theorems.Thm_lean_workbook_plus_26009
-- name    : lean_workbook_plus_26009
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1b6b058d-19de-4f13-b0b8-15b49f1ad0d3
-- statement:
--   Let a,b,c be any real number and a,b,c>0.prove that: \n $ \frac {a}{b} + \frac {b}{c} + \frac {c}{a}\geq\frac {a + b}{b + c} + \frac {b + c}{a + b} + 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26009 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1   :=  by sorry

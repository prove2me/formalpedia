-- Prove2me | Theorems.Thm_lean_workbook_plus_24
-- name    : lean_workbook_plus_24
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5b8db499-4c33-4dc0-b612-887ddf73e7d1
-- statement:
--   For positive real numbers $a,b,c,$ have \n $\frac 1{a} + \frac 1{b} + \frac 1{c} \ge 2\left(\frac 1{b+c} + \frac 1{c+a} + \frac 1{a+b}\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c ≥ 2 * (1 / (b + c) + 1 / (c + a) + 1 / (a + b))   :=  by sorry

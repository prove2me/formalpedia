-- Prove2me | Theorems.Thm_lean_workbook_plus_74946
-- name    : lean_workbook_plus_74946
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b368fa4f-0a55-44ad-a018-658015a03ec9
-- statement:
--   $ \frac { 1}{a + b} + \frac { 1}{b + c} + \frac { 1}{c + a}\geq \frac {9}{2(a + b + c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74946 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ 9 / (2 * (a + b + c))   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_18299
-- name    : lean_workbook_plus_18299
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0bb3229f-5ccb-441c-971f-857f26803fcb
-- statement:
--   Prove that if $a,b,c$ are positive real numbers, then $\frac{a}{b+2c}+\frac{b}{c+2a}+\frac{c}{a+2b}\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18299 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)) ≥ 1   :=  by sorry

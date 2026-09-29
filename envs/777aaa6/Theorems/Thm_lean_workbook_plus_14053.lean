-- Prove2me | Theorems.Thm_lean_workbook_plus_14053
-- name    : lean_workbook_plus_14053
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a42d5558-b301-4f5f-9a3b-a090c42df83c
-- statement:
--   Prove that, if a, b, c are positive real numbers, \n $$ \frac{a}{bc}+\frac{b}{ac}+\frac{c}{ab} \geq \frac{2}{a}+\frac{2}{b}-\frac{2}{c}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14053 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b / c + b / a / c + c / a / b ≥ 2 / a + 2 / b - 2 / c   :=  by sorry

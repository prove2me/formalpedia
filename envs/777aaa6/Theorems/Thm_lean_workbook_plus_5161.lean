-- Prove2me | Theorems.Thm_lean_workbook_plus_5161
-- name    : lean_workbook_plus_5161
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/098e20a0-0cae-40f7-9d2d-d0074bee539f
-- statement:
--   Prove that if $a_1,a_2$ are positive reals, then $\frac{a_1+a_2}{2} \geq \sqrt{a_1a_2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5161 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) / 2 ≥ Real.sqrt (a * b)   :=  by sorry

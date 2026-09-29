-- Prove2me | Theorems.Thm_lean_workbook_plus_26678
-- name    : lean_workbook_plus_26678
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8ff4bee0-3b5c-4640-bc92-41422fca5aa2
-- statement:
--   Prove that if $a_1,a_2$ are positive reals, then $\frac{a_1+a_2}{2} \geq \sqrt{a_1a_2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26678 (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) : (a1 + a2) / 2 ≥ Real.sqrt (a1 * a2)   :=  by sorry

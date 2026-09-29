-- Prove2me | Theorems.Thm_lean_workbook_plus_60494
-- name    : lean_workbook_plus_60494
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/95bb9098-dfbd-4098-a2ca-88ff8fcb04f7
-- statement:
--   Prove that $\log \left ( \tan \left ( \frac{\pi}{4}-a \right ) \right ) =-\log \left ( \tan \left ( \frac{\pi}{4}+a \right ) \right )$ for $0<a<\frac{\pi}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60494 (a : ℝ) (ha : 0 < a ∧ a < Real.pi / 4) : Real.log (Real.tan (Real.pi / 4 - a)) = -Real.log (Real.tan (Real.pi / 4 + a))   :=  by sorry

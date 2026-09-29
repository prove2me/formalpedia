-- Prove2me | Theorems.Thm_lean_workbook_plus_67003
-- name    : lean_workbook_plus_67003
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a3978486-7726-4f8a-986b-f8dda2fee828
-- statement:
--   Prove that $\sqrt{1+(\pi-x)^2}-\sqrt{1+x^2} \ge 0$ $\forall x \in [0,\frac{\pi}{2}]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67003 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) : 0 ≤ Real.sqrt (1 + (π - x) ^ 2) - Real.sqrt (1 + x ^ 2)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_8810
-- name    : lean_workbook_plus_8810
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4cb6ee1f-83cc-4be2-b63b-16815b307fda
-- statement:
--   Prove that $\sqrt{x\cos x} \le \frac{x + \cos x}{2}$ for $x\in [0,\frac{\pi}{2}]$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8810 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) :
  Real.sqrt (x * Real.cos x) ≤ (x + Real.cos x) / 2   :=  by sorry

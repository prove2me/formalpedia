-- Prove2me | Theorems.Thm_lean_workbook_plus_11366
-- name    : lean_workbook_plus_11366
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/90ef2907-1f6d-4068-94b1-1102b9072d53
-- statement:
--   Prove that $\sin x+\cos x\leq\sqrt 2$ , where $\ x\in\left(0,\frac{\pi}{2}\right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11366 (x : ℝ) (hx : 0 < x ∧ x < Real.pi / 2) :
  Real.sin x + Real.cos x ≤ Real.sqrt 2   :=  by sorry

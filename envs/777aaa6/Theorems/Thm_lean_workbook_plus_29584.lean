-- Prove2me | Theorems.Thm_lean_workbook_plus_29584
-- name    : lean_workbook_plus_29584
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/01f0487c-5add-46d1-866c-d75521a3f0a7
-- statement:
--   Prove that $g=\cos 2x+\frac{3}{2}\cos 2(y+x)-\cos 2y < \frac{3}{2}$ for $0 < x, y < \frac{\pi}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29584 (x y : ℝ) (hx : 0 < x ∧ x < π/2) (hy : 0 < y ∧ y < π/2) :
  Real.cos 2*x + 3/2 * Real.cos 2*(y + x) - Real.cos 2*y < 3/2   :=  by sorry

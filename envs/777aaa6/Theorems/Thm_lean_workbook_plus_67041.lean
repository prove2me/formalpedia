-- Prove2me | Theorems.Thm_lean_workbook_plus_67041
-- name    : lean_workbook_plus_67041
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/bd66834e-9440-43a9-bffe-ada43f23b79f
-- statement:
--   Thus it suffices to prove that $-4\cos^2 x + 4 \cos x + 2 \leq 3$ i.e. $(2\cos x - 1)^2 \geq 0$ which is obvious.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67041  (x : ℝ) :
  -4 * Real.cos x ^ 2 + 4 * Real.cos x + 2 ≤ 3   :=  by sorry

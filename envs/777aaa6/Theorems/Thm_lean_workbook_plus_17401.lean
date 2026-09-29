-- Prove2me | Theorems.Thm_lean_workbook_plus_17401
-- name    : lean_workbook_plus_17401
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/380ac5e2-9023-4ce3-bc77-a1a103e9addb
-- statement:
--   Prove that $\cos(3x) = 4\cos^{3}(x) - 3\cos(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17401 (x : ℝ) : Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x   :=  by sorry

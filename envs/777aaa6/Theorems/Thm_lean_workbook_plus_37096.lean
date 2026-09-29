-- Prove2me | Theorems.Thm_lean_workbook_plus_37096
-- name    : lean_workbook_plus_37096
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4e01df98-559d-4440-ac70-e03a7e555d23
-- statement:
--   $\cos 2y-\cos 2x=2\sin(x+y)\sin (x-y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37096 : ∀ x y : ℝ, Real.cos (2 * y) - Real.cos (2 * x) = 2 * Real.sin (x + y) * Real.sin (x - y)   :=  by sorry

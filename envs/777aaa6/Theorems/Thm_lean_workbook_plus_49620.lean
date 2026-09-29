-- Prove2me | Theorems.Thm_lean_workbook_plus_49620
-- name    : lean_workbook_plus_49620
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0d42f255-88bc-46d4-bb17-9b0cb620d740
-- statement:
--   2) $u\in\left\{0,\frac 12\right\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49620 (u : ℝ) (hu : u ∈ ({0, 1 / 2} : Finset ℝ)) : u = 0 ∨ u = 1 / 2   :=  by sorry

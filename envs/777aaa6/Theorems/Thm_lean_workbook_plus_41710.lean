-- Prove2me | Theorems.Thm_lean_workbook_plus_41710
-- name    : lean_workbook_plus_41710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/418e15bf-ed6d-4ed3-a7b7-a5e3ba4a8ced
-- statement:
--   Prove that $\sqrt{x^{2}-3} \leq 2x-3$ for $x \geq \sqrt{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41710 (x : ℝ) (hx : x ≥ Real.sqrt 3) : Real.sqrt (x ^ 2 - 3) ≤ 2 * x - 3   :=  by sorry

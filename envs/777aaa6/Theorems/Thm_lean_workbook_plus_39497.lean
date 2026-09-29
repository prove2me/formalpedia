-- Prove2me | Theorems.Thm_lean_workbook_plus_39497
-- name    : lean_workbook_plus_39497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f6872047-137d-4642-92b0-8cd20087d3aa
-- statement:
--   Prove the inequality $(\sqrt{3}x - 1)^2(2x + \sqrt{3}) \geq 0$ for $x \in (0, 1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39497 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  0 ≤ ((Real.sqrt 3) * x - 1)^2 * (2 * x + Real.sqrt 3)   :=  by sorry

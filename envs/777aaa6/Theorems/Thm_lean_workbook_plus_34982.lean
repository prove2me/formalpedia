-- Prove2me | Theorems.Thm_lean_workbook_plus_34982
-- name    : lean_workbook_plus_34982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/6d29dc5d-66e6-418b-bf82-392f782befd1
-- statement:
--   Use part (i) to find the greatest value of $xy^{2}$ in the region of the $x-y$ plane given by $x \geq0, y \geq 0$ and $x+2y \leq 3$ . For what values of $x$ and $y$ is this greatest value achieved?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34982 (x y : ℝ) (hx: x ≥ 0 ∧ y ≥ 0 ∧ x + 2*y ≤ 3): x*y^2 ≤ 1   :=  by sorry

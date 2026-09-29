-- Prove2me | Theorems.Thm_lean_workbook_plus_6695
-- name    : lean_workbook_plus_6695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/fa7a33e9-d1ad-43f7-a350-12ecf970c08e
-- statement:
--   prove that $\frac{1}{2x} \ge \frac{3}{2}-2x^2 \; \forall x\in (0;1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6695 (x : ℝ) (hx : 0 < x ∧ x < 1) : (1 / (2 * x)) ≥ (3 / 2) - 2 * x ^ 2   :=  by sorry

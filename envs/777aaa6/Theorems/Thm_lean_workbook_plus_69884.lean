-- Prove2me | Theorems.Thm_lean_workbook_plus_69884
-- name    : lean_workbook_plus_69884
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0c478a4c-5c40-48c1-b1ff-56bc87b0e7bc
-- statement:
--   I think the domain is $V = \{M(x; y) \in \Re^2 : (-2 < x < 2) \wedge (y < \frac{x^2}{4}) \wedge (y > x - 1) \wedge (y > -x + 1)\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69884 (x y : ℝ) : (-2 < x ∧ x < 2 ∧ y < x^2 / 4 ∧ y > x - 1 ∧ y > -x + 1) ↔ -2 < x ∧ x < 2 ∧ y < x^2 / 4 ∧ y > x - 1 ∧ y > -x + 1   :=  by sorry

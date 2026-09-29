-- Prove2me | Theorems.Thm_lean_workbook_plus_63196
-- name    : lean_workbook_plus_63196
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/199b2fd1-d4a8-47cd-b5ad-8fe5084b5d2e
-- statement:
--   $x^2+y^2+z^2 \ge \frac{x+y+z}{2} \ge \frac{3-x-y-z}{2}$ , by proof1 and by Nesbit
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63196 : ∀ x y z : ℝ, x^2 + y^2 + z^2 ≥ (x + y + z) / 2 ∧ (x + y + z) / 2 ≥ (3 - x - y - z) / 2   :=  by sorry

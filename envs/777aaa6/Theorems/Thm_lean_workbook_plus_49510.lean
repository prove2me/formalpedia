-- Prove2me | Theorems.Thm_lean_workbook_plus_49510
-- name    : lean_workbook_plus_49510
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/282892d3-5101-4c46-889e-49c58ec9f6f1
-- statement:
--   Let $x,y\ge0$ and $x+y=1$. Prove that: $x^2y^2(x^2+y^2)\le2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49510 : ∀ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x + y = 1 → x^2*y^2*(x^2+y^2) ≤ 2   :=  by sorry

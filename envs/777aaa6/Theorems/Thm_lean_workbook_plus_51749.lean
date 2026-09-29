-- Prove2me | Theorems.Thm_lean_workbook_plus_51749
-- name    : lean_workbook_plus_51749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7559272e-48c1-4674-a815-bd2f107973f0
-- statement:
--   Prove that if $x$ and $y$ are positive real numbers that $(x^4 + y^4)(x^2 + y^2) \geq 2x^3y^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51749 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^4 + y^4) * (x^2 + y^2) ≥ 2 * x^3 * y^3   :=  by sorry

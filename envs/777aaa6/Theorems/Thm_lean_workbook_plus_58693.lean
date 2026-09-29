-- Prove2me | Theorems.Thm_lean_workbook_plus_58693
-- name    : lean_workbook_plus_58693
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/be113e32-0079-4c94-8335-474e0b0fb097
-- statement:
--   If $x, y$ are positive reals such that $(x-y)(x-1)\le 0$ then prove that $\dfrac{x+2y}{y+2x}\ge \dfrac{y+2xy}{x+2xy}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58693 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 0 < x + y) (h : (x - y) * (x - 1) ≤ 0) : (x + 2 * y) / (y + 2 * x) ≥ (y + 2 * x * y) / (x + 2 * x * y)   :=  by sorry

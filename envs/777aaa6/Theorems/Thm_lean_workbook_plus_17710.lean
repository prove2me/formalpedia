-- Prove2me | Theorems.Thm_lean_workbook_plus_17710
-- name    : lean_workbook_plus_17710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f8b91afb-a2ed-482f-936b-e2d6ef512a9d
-- statement:
--   Proposition. It holds $\forall x,y,z\in\mathbb{R}_{\ge 0}$ that $(x+y)(y+z)(z+x)\ge(x+2y-z)(y+2z-x)(z+2x-y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17710 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y) * (y + z) * (z + x) ≥ (x + 2 * y - z) * (y + 2 * z - x) * (z + 2 * x - y)   :=  by sorry

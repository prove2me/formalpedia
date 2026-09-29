-- Prove2me | Theorems.Thm_lean_workbook_plus_55671
-- name    : lean_workbook_plus_55671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/36712a29-1c4e-418a-8591-085ab357415a
-- statement:
--   Prove that $(x-y)^2(y-z)^2+6(x-y)(y-z)\geq 0$ for $x\geq y\geq z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55671 (x y z : ℝ) (h₁ : x ≥ y) (h₂ : y ≥ z) : (x - y) ^ 2 * (y - z) ^ 2 + 6 * (x - y) * (y - z) ≥ 0   :=  by sorry

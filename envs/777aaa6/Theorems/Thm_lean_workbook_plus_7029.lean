-- Prove2me | Theorems.Thm_lean_workbook_plus_7029
-- name    : lean_workbook_plus_7029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0a52eea1-2edb-41ce-ae42-1fd93481f4f1
-- statement:
--   Prove that $(x^3+y^3)(x+y) \geq (x^2+y^2)^2$ for all positive real numbers $x,y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7029 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x ^ 3 + y ^ 3) * (x + y) ≥ (x ^ 2 + y ^ 2) ^ 2   :=  by sorry

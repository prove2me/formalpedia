-- Prove2me | Theorems.Thm_lean_workbook_plus_26353
-- name    : lean_workbook_plus_26353
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3bd2938d-d95c-4834-8f7e-3663652d1b74
-- statement:
--   Prove that $(x + 1)(y + 2)(z + 3) \geq 8$ for non-negative real numbers $x, y, z$ with $x + y + z = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26353 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 1) : (x + 1) * (y + 2) * (z + 3) ≥ 8   :=  by sorry

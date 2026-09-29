-- Prove2me | Theorems.Thm_lean_workbook_plus_44371
-- name    : lean_workbook_plus_44371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/055a0664-d11c-4b38-82bc-f4d22388d666
-- statement:
--   Prove $x^3+y^3+z^3-3xyz \ge 0$ for $x, y, z \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44371 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x^3 + y^3 + z^3 - 3 * x * y * z ≥ 0   :=  by sorry

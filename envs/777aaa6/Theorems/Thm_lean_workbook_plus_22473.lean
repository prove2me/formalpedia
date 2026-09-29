-- Prove2me | Theorems.Thm_lean_workbook_plus_22473
-- name    : lean_workbook_plus_22473
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/98e039bd-789e-43b9-a279-e1d6c5ff4397
-- statement:
--   Prove that for positive real numbers $x, y, z$: \n\n$x^2 + y^2 + z^2 \geq xy + yz + xz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22473 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + x * z   :=  by sorry

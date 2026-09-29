-- Prove2me | Theorems.Thm_lean_workbook_plus_31530
-- name    : lean_workbook_plus_31530
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/eb7f9b8a-26f7-4d74-bc8b-125705c72293
-- statement:
--   Prove that for positive reals $x, y, z$, $(x + y + z)^3 \geq 27xyz$ without using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31530 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 3 ≥ 27 * x * y * z   :=  by sorry

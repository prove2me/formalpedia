-- Prove2me | Theorems.Thm_lean_workbook_plus_76556
-- name    : lean_workbook_plus_76556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2836a6b1-59a3-4e5a-9ae7-be1e4481f61b
-- statement:
--   Prove that, if $x, $ and $z$ are non-negative and $xyz \geq 1$ , then $(x+1)(y+1)(z+1) \geq 8$ . Is the converse true?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76556 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x*y*z ≥ 1) : (x + 1) * (y + 1) * (z + 1) ≥ 8   :=  by sorry

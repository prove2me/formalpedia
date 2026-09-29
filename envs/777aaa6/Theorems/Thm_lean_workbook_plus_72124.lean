-- Prove2me | Theorems.Thm_lean_workbook_plus_72124
-- name    : lean_workbook_plus_72124
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/aee1d5f4-3cdb-4215-b11c-93878aae235c
-- statement:
--   Let $x,y,z \geq 0, x(y+z)(x+y+z)=1$, prove that: $(x+y+z)^3 \geq 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72124 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x * (y + z) * (x + y + z) = 1) : (x + y + z) ^ 3 ≥ 4   :=  by sorry

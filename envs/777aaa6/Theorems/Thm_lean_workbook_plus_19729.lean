-- Prove2me | Theorems.Thm_lean_workbook_plus_19729
-- name    : lean_workbook_plus_19729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8cac805e-8acb-4b32-9988-1082374e6e4f
-- statement:
--   And so $x=\frac{v-u-4}8$ and $(2y+1)^2=\frac{u+v-6}2$ where $uv=12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19729 (x y : ℝ) (u v : ℝ) : (u * v = 12 ∧ x = (v - u - 4) / 8 ∧ (2 * y + 1) ^ 2 = (u + v - 6) / 2) ↔ (u * v = 12 ∧ (u + v - 6) / 2 = (2 * y + 1) ^ 2 ∧ x = (v - u - 4) / 8)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_66146
-- name    : lean_workbook_plus_66146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b8b09ffd-a682-4f15-a9df-27818f3a1912
-- statement:
--   Prove that $4a^3+2a^2+13a-1\geq 0$ given $1\geq a\geq \dfrac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66146 (a : ℝ) (ha1 : 1 ≥ a) (ha2 : a ≥ 1/3) : 4 * a ^ 3 + 2 * a ^ 2 + 13 * a - 1 ≥ 0   :=  by sorry

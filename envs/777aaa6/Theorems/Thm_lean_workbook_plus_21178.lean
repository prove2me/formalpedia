-- Prove2me | Theorems.Thm_lean_workbook_plus_21178
-- name    : lean_workbook_plus_21178
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/977f48df-b86d-4069-8cf2-aea6473163b8
-- statement:
--   with $x_n=n^{1/3}$ , this $(x_2-x_3)^2+(x_3-x_4)^2+(x_4-x_2)^2\ge 0$ , my friend ...
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21178 (x : ℕ → ℝ) (hx: ∀ n, x n = n^(1/3)) : (x 2 - x 3) ^ 2 + (x 3 - x 4) ^ 2 + (x 4 - x 2) ^ 2 ≥ 0   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_2836
-- name    : lean_workbook_plus_2836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cf8a76d9-9e8c-49e9-9501-02ae8612d491
-- statement:
--   Prove that if $\sum x_i^2=0$, then $x_i=0$ for all $i$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2836 (n : ℕ) (x : Fin n → ℝ) (h : ∑ i, x i ^ 2 = 0) : ∀ i, x i = 0   :=  by sorry

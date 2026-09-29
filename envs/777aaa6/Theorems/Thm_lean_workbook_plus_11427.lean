-- Prove2me | Theorems.Thm_lean_workbook_plus_11427
-- name    : lean_workbook_plus_11427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/cd7003ae-e778-4d4d-a700-28e21e601ada
-- statement:
--   Prove that for $k\geq 1$, $1+\frac{1}{k}\leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11427 (k : ℕ) (h : 1 ≤ k) : (1 : ℝ) + 1/k ≤ 2   :=  by sorry

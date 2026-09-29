-- Prove2me | Theorems.Thm_lean_workbook_plus_75083
-- name    : lean_workbook_plus_75083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/30639ad5-9619-4257-9814-d0271da69d70
-- statement:
--   Any odd positive integer $N$ has a multiple $M$ of the form $4m^2-1$ , namely $M = N(N+2) = (N+1)^2 - 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75083 (n : ℤ) (h : n > 0 ∧ Odd n) : ∃ m : ℤ, n * (n + 2) = 4 * m ^ 2 - 1   :=  by sorry

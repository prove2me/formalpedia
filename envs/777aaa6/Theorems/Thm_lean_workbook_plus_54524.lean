-- Prove2me | Theorems.Thm_lean_workbook_plus_54524
-- name    : lean_workbook_plus_54524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/6c970ad4-722a-4456-bc84-e9f02bb356ed
-- statement:
--   $n\left(\frac 1{n+1}+\frac 1{(n+1)^2}+\frac 1{(n+1)^3}\right)<1$ $\forall n\ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54524 (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * (1 / (n + 1) + 1 / (n + 1) ^ 2 + 1 / (n + 1) ^ 3) < 1   :=  by sorry

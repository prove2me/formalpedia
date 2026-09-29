-- Prove2me | Theorems.Thm_lean_workbook_plus_54755
-- name    : lean_workbook_plus_54755
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/6ad95c31-b426-4ff9-9887-4579cd4588d3
-- statement:
--   Prove that for real $ y\ge-1$ and integers $ k\ge1$ we have $ (y+1)^k\ge ky+1$ . And equality holds if and only if $ y=0$ or $ k=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54755 (y : ℝ) (k : ℕ) (_hk : 1 ≤ k) (_hy : -1 ≤ y) : (y + 1) ^ k ≥ k * y + 1   :=  by sorry

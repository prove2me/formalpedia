-- Prove2me | Theorems.Thm_lean_workbook_plus_795
-- name    : lean_workbook_plus_795
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/51988868-9eea-467e-892f-d8e7e49eae2c
-- statement:
--   $\binom{n}{1}$ is odd tells us $n$ is odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_795 (n : ℕ) (h : n ≠ 0) : Odd (choose n 1) → Odd n   :=  by sorry

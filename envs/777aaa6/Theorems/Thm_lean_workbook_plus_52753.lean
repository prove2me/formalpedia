-- Prove2me | Theorems.Thm_lean_workbook_plus_52753
-- name    : lean_workbook_plus_52753
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/88d77509-4952-46d0-80b3-2c841d15065e
-- statement:
--   Prove that $\binom{n}{n-1}=n$ for any positive integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52753 (n : ℕ) (h : n ≠ 0) : choose n (n-1) = n   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_64396
-- name    : lean_workbook_plus_64396
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b094945a-2c0c-4ab6-8454-10aba33ef7a7
-- statement:
--   Prove that, $\binom{n}{2}+\binom{n}{1}=\binom{n+1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64396 (n : ℕ) : choose n 2 + choose n 1 = choose (n + 1) 2   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_78721
-- name    : lean_workbook_plus_78721
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f2ab4521-6e08-485f-ac99-3b6c5561758e
-- statement:
--   Prove that $F_{2n+1}= F_{n}^{2}+F_{n+1}^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78721 (n : ℕ) : fib (2 * n + 1) = fib n ^ 2 + fib (n + 1) ^ 2   :=  by sorry

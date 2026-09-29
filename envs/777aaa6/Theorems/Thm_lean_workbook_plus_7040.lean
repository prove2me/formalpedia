-- Prove2me | Theorems.Thm_lean_workbook_plus_7040
-- name    : lean_workbook_plus_7040
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3814ba94-5866-4ccc-90fd-abc699a4d650
-- statement:
--   Prove that $|a_{1}+a_{2}+a_{3}+\ldots+a_{n}| \leq |a_{1}|+|a_{2}|+|a_{3}|+\ldots+|a_{n}|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7040 (n : ℕ) (a : ℕ → ℤ) : |∑ i in Finset.range n, a i| ≤ ∑ i in Finset.range n, |a i|   :=  by sorry

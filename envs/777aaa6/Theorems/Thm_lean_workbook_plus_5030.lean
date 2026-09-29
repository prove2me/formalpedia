-- Prove2me | Theorems.Thm_lean_workbook_plus_5030
-- name    : lean_workbook_plus_5030
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f1f7e5ba-3ede-4747-a4af-91bf8fe76dd3
-- statement:
--   An arithmetic sequence $a_{1}, a_{2}, a_{3},\cdots a_{19}$ has $19$ terms. Find $a_{1}+a_{2}+\cdots+a_{18}+a_{19}$ given that $a_{1}+a_{7}+a_{14}+a_{18}=200$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5030 (a : ℕ → ℕ) (h : a 1 + a 7 + a 14 + a 18 = 200) : ∑ i in Finset.range 19, a i = 190   :=  by sorry

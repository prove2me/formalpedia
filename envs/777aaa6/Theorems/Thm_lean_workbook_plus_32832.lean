-- Prove2me | Theorems.Thm_lean_workbook_plus_32832
-- name    : lean_workbook_plus_32832
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/94f33dba-01ca-43a6-b073-ee03a070f8f4
-- statement:
--   Prove $a_{n} = \\frac{(n-1)!!}{(n-2)!!}$ for the sequence defined by $a_1=1,\ a_na_{n+1}=n\ (n=1,\ 2,\ \cdots).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32832 : ∃ a : ℕ → ℝ, a 1 = 1 ∧ ∀ n, a (n + 1) * a n = n ∧ a n = ((n - 1)!! / (n - 2)!!)   :=  by sorry

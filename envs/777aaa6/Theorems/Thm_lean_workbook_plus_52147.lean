-- Prove2me | Theorems.Thm_lean_workbook_plus_52147
-- name    : lean_workbook_plus_52147
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6444c33c-34ba-49e5-bda8-a1d716a6c1b3
-- statement:
--   Prove by induction that $ n-1<\frac{(n+1)!}{1!+2!+3!+...+n!}<n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52147 (n : ℕ) : n - 1 < (n + 1)! / (∑ k in Finset.range n, k!) ∧ (n + 1)! / (∑ k in Finset.range n, k!) < n   :=  by sorry

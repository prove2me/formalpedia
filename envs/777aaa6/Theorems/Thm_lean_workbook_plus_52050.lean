-- Prove2me | Theorems.Thm_lean_workbook_plus_52050
-- name    : lean_workbook_plus_52050
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9e1bf98e-9dfd-4168-ad65-b4885ab1f8f2
-- statement:
--   Prove that $\sum_{k=0}^{25} \binom{25}{k} = 2^{25}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52050 : ∑ k in Finset.range 26, choose 25 k = 2^25   :=  by sorry

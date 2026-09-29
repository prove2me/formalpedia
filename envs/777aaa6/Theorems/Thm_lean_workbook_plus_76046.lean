-- Prove2me | Theorems.Thm_lean_workbook_plus_76046
-- name    : lean_workbook_plus_76046
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bf7b2b5e-525b-43e6-8de8-e0e4efd3b6eb
-- statement:
--   What is the value of $\sum_{n=1}^{100}n$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76046 : ∑ n in Finset.range 101, n = 5050   :=  by sorry

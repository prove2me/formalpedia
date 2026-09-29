-- Prove2me | Theorems.Thm_lean_workbook_plus_63124
-- name    : lean_workbook_plus_63124
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/62e2a48b-31e3-4cbc-b06e-36bbc0711e00
-- statement:
--   Prove that for all $n=2,3,...$ $(1-1/2^3)(1-1/3^3)...(1-1/n^3)>1/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63124 : ∀ n : ℕ, 1 / 2 < ∏ i in Finset.Icc 2 n, (1 - 1 / i ^ 3)   :=  by sorry

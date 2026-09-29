-- Prove2me | Theorems.Thm_lean_workbook_plus_15937
-- name    : lean_workbook_plus_15937
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/2a4cbe2b-3d34-42cc-959b-eda5c6d60c8d
-- statement:
--   Prove that $7|1^{100}+2^{100}+\cdots+1981^{100}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15937 : 7 ∣ (∑ i in Finset.Icc 1 1981, i^100)   :=  by sorry

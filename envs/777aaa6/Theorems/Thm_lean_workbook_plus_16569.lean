-- Prove2me | Theorems.Thm_lean_workbook_plus_16569
-- name    : lean_workbook_plus_16569
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/aed5c8f8-17a3-430c-ba69-8b80616bf7da
-- statement:
--   What is the average of the first $9$ positive integers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16569 (n : ℕ) : (∑ i in Finset.range 9, i + 1) / 9 = 5   :=  by sorry

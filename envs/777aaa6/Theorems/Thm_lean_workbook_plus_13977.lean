-- Prove2me | Theorems.Thm_lean_workbook_plus_13977
-- name    : lean_workbook_plus_13977
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/baac99a2-0968-4a1a-bef9-feb34fffa3bb
-- statement:
--   (a) What is the last digit of the sum $1^{2012}+2^{2012}+3^{2012}+4^{2012}+5^{2012}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13977 : (∑ i in Finset.range 6, (i + 1)^2012) % 10 = 5   :=  by sorry

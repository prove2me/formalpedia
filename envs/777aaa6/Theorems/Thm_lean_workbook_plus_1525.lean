-- Prove2me | Theorems.Thm_lean_workbook_plus_1525
-- name    : lean_workbook_plus_1525
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3ffa12fa-c991-47e8-8092-e4799fa29f1e
-- statement:
--   What is the sum of $2^0+2^1+2^2+2^3+2^4+2^5+2^6+2^7+2^8+2^9$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1525 (x : ℕ) (hx: x = 1023) : ∑ i in Finset.range 10, 2^i = x   :=  by sorry

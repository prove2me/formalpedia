-- Prove2me | Theorems.Thm_lean_workbook_plus_52046
-- name    : lean_workbook_plus_52046
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1c2e2990-d6b6-4b64-965b-20474b14ea9f
-- statement:
--   Find $1/(2^1)+2/(2^2)+3/(2^3)+...+10/(2^{10})$ in fractional form.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52046 : ∑ i in Finset.Icc 1 10, (i + 1) / (2 ^ i) = 509 / 256   :=  by sorry

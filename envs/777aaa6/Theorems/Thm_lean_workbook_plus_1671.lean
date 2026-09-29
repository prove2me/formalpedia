-- Prove2me | Theorems.Thm_lean_workbook_plus_1671
-- name    : lean_workbook_plus_1671
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/823b88e6-2c27-47ee-8d02-0b1526dad3be
-- statement:
--   Find $1\\times100 +2\\times99...+49\\times52+50\\times51$ without a calculator.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1671 : ∑ k in Finset.Icc 1 50, (k * (101 - k)) = 85850   :=  by sorry

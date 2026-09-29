-- Prove2me | Theorems.Thm_lean_workbook_plus_44897
-- name    : lean_workbook_plus_44897
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/9b2680fc-dec2-4d7c-8271-dc4967b6dc05
-- statement:
--   What is $1+2+3+4+5+....+10000$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44897 : ∑ i in Finset.range 10000, i = 50005000   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_82803
-- name    : lean_workbook_plus_82803
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.51614+00:00
-- url     : https://prove2.me/theorems/b2693c89-c9ac-4298-a45d-6e85989569e4
-- statement:
--   What is $1\cdot2\cdot3 + 2\cdot3\cdot4 + 3\cdot4\cdot5 + ... + 20\cdot21\cdot22$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82803 : ∑ k in Finset.Icc 1 20, k * (k + 1) * (k + 2) = 53130   :=  by sorry

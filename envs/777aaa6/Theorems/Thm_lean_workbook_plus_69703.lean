-- Prove2me | Theorems.Thm_lean_workbook_plus_69703
-- name    : lean_workbook_plus_69703
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/67473fa7-9079-4f28-bd07-6fc6069bf040
-- statement:
--   Therefore the answer is $ \binom{11}{0}+\binom{10}{1}+\binom{9}{2}+\binom 83 + \binom 74 + \binom 65 = \boxed{144}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69703 ∑ k in Finset.range 6, (11-k).choose k = 144   :=  by sorry

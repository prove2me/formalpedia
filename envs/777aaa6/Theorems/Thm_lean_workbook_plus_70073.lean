-- Prove2me | Theorems.Thm_lean_workbook_plus_70073
-- name    : lean_workbook_plus_70073
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/82a099b0-e2e0-4343-9cd0-7fb39b45ef17
-- statement:
--   The number of combinations with four circles is given by $\binom{4}{0}+\binom{4}{1}+\binom{4}{2}+\binom{4}{3}+\binom{4}{4}=16$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70073 ∑ k in Finset.range 5, (Nat.choose 4 k) = 16   :=  by sorry

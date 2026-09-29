-- Prove2me | Theorems.Thm_lean_workbook_plus_52987
-- name    : lean_workbook_plus_52987
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/afcc8125-59f5-4001-980b-5251c0600fbc
-- statement:
--   Prove that $(ab)^m+(bc)^m+(ca)^m\leq 3$ for $a+b+c=3$ and $m=4/3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52987 ∀ a b c : ℝ, a + b + c = 3 ∧ m = 4/3 → (a * b) ^ m + (b * c) ^ m + (c * a) ^ m ≤ 3   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_40913
-- name    : lean_workbook_plus_40913
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/59706753-d5a6-43bb-a827-3df7b805963a
-- statement:
--   If $ |ax^{2}+bx+c|\leq 1 $ for all $ x \in [-1,1]$ . Then $$|a|+|b|+|c|\le 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40913 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, abs (a * x ^ 2 + b * x + c) ≤ 1) : abs a + abs b + abs c ≤ 3   :=  by sorry

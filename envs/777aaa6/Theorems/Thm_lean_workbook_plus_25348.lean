-- Prove2me | Theorems.Thm_lean_workbook_plus_25348
-- name    : lean_workbook_plus_25348
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0535327a-8593-4333-82ac-7f93df3f96ef
-- statement:
--   Assume wlog $ a \ge b \ge c$ . Then $ (c - a)^2 \ge (a - b)^2 + (b - c)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25348 (a b c : ℝ) (h : a ≥ b ∧ b ≥ c) : (c - a) ^ 2 ≥ (a - b) ^ 2 + (b - c) ^ 2   :=  by sorry

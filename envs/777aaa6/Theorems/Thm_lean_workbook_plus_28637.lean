-- Prove2me | Theorems.Thm_lean_workbook_plus_28637
-- name    : lean_workbook_plus_28637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4ea9fd19-2659-448b-b873-d8a912a4d0a0
-- statement:
--   Because $0\leq a\leq b\leq c\leq d\leq e \Rightarrow d+e\geq c+e\geq d+b\geq a+c\geq a+b\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28637 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0   :=  by sorry

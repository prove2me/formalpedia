-- Prove2me | Theorems.Thm_lean_workbook_plus_66893
-- name    : lean_workbook_plus_66893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/329c7046-cce3-4ffc-83c8-6d7b1354a803
-- statement:
--   Given $a\leq b\leq c$, prove that $a+b\leq c+a\leq b+c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66893 (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a + b ≤ c + a ∧ c + a ≤ b + c   :=  by sorry

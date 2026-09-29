-- Prove2me | Theorems.Thm_lean_workbook_plus_25571
-- name    : lean_workbook_plus_25571
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/039bba31-95e4-49a1-8fd6-f89d5d4f3135
-- statement:
--   Let $0<b \leq a \leq 4$ và $a+b \leq 7$ , Prove $a^{2}+b^{2} \leq 25$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25571 (a b : ℝ) (h₁ : 0 < b ∧ b ≤ a ∧ a ≤ 4 ∧ a + b ≤ 7) : a^2 + b^2 ≤ 25   :=  by sorry

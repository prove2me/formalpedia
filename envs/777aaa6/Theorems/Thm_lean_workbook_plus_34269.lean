-- Prove2me | Theorems.Thm_lean_workbook_plus_34269
-- name    : lean_workbook_plus_34269
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9475f944-38f6-4780-b166-8b0b3327a1a3
-- statement:
--   Prove that, $(a+3b)(b+4c)(c+2a) \geq 60abc$ for all real numbers $0\leq a\leq b\leq c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34269 : ∀ a b c : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ c → (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry

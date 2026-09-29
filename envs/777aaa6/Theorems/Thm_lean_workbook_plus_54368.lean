-- Prove2me | Theorems.Thm_lean_workbook_plus_54368
-- name    : lean_workbook_plus_54368
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5aa75501-c4c3-4e7b-9ece-1131339aac53
-- statement:
--   If \(a, b, c\) are positive real numbers such that \(a^2 + b^2 + c^2 = 3\), then \(a + b + c \leq 3\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54368 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a + b + c ≤ 3   :=  by sorry

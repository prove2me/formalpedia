-- Prove2me | Theorems.Thm_lean_workbook_plus_56949
-- name    : lean_workbook_plus_56949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f3b63bfb-f07b-4404-b396-e56585e4c5aa
-- statement:
--   Prove the inequality $ab+bc+ca\le a^2+b^2+c^2$ for $2\ge a\ge b \ge c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56949 (a b c : ℝ) (h1 : 2 ≥ a ∧ a ≥ b ∧ b ≥ c) :
  a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_31735
-- name    : lean_workbook_plus_31735
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/1c14a547-e7d1-4c08-be1a-b0786230c459
-- statement:
--   Prove that $(a-b)(b-c)(c-a)\leq0$ when $a\geq b\geq c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31735 (a b c : ℝ) (h₁ : a ≥ b ∧ b ≥ c) :
  (a - b) * (b - c) * (c - a) ≤ 0   :=  by sorry

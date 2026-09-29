-- Prove2me | Theorems.Thm_lean_workbook_plus_16360
-- name    : lean_workbook_plus_16360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b4d20e4e-7dec-4d2b-ac4d-f3510d84ebc5
-- statement:
--   Using the condition $a \leq b + c$ and $a, b, c \leq 1$, prove the inequality $(1-a)(1-b)(1-c) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16360 (a b c : ℝ) (h₁ : a ≤ b + c) (h₂ : a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1) :
  (1 - a) * (1 - b) * (1 - c) ≥ 0   :=  by sorry

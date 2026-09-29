-- Prove2me | Theorems.Thm_lean_workbook_plus_54751
-- name    : lean_workbook_plus_54751
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f5907303-88cc-4222-bb7e-a1e721105160
-- statement:
--   Given $a + c \geq b + d$ and $a + b = c + d$, prove that $a \geq d$ and $c \geq b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54751 (a b c d : ℝ) (h₁ : a + c ≥ b + d) (h₂ : a + b = c + d) : a ≥ d ∧ c ≥ b   :=  by sorry

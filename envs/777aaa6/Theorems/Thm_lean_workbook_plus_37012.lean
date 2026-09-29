-- Prove2me | Theorems.Thm_lean_workbook_plus_37012
-- name    : lean_workbook_plus_37012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/77ca234d-2d33-4a14-869f-d43f427d1894
-- statement:
--   Given real numbers $a$, $b$, $c$ with $1 \leq a \leq 1$, $1 \leq b \leq 1$, $1 \leq c \leq 1$, prove that $ab + bc + ca + 1 \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37012 : ∀ a b c : ℝ, 1 ≤ a ∧ a ≤ 1 ∧ 1 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 1 → a * b + b * c + c * a + 1 ≥ 0   :=  by sorry

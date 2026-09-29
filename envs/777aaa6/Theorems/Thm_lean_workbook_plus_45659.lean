-- Prove2me | Theorems.Thm_lean_workbook_plus_45659
-- name    : lean_workbook_plus_45659
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b2105784-3970-48b7-8644-4a9964cfc5bc
-- statement:
--   Prove that $a^2 + b^2 \geq \frac{c^2}{2}$ given $a + b \geq c \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45659 (a b c : ℝ) (h₁ : a + b ≥ c) (h₂ : c ≥ 0) : a^2 + b^2 ≥ c^2 / 2   :=  by sorry

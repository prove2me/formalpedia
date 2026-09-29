-- Prove2me | Theorems.Thm_lean_workbook_plus_41699
-- name    : lean_workbook_plus_41699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/38c7527e-5cf1-4348-be03-981f2643ac4d
-- statement:
--   Given $a \geq 1$ and $b + c \leq -1$, prove that $a^4 + b^4 + c^4 \geq a^3 + b^3 + c^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41699 (a b c : ℝ) (h₁ : a ≥ 1) (h₂ : b + c ≤ -1) : a^4 + b^4 + c^4 ≥ a^3 + b^3 + c^3   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_2480
-- name    : lean_workbook_plus_2480
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2a9fda33-5b89-4064-8424-bc4ca93bbb80
-- statement:
--   Prove that $\lim_{h \to 0} \frac{1}{h} \exp(-1/h^2) = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2480 : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ h : ℝ, h > 0 ∧ h < 1 / N → |1 / h * exp (-1 / h^2)| < ε   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_72039
-- name    : lean_workbook_plus_72039
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c519c57d-3b0f-4c4e-b4e6-4973a0495b92
-- statement:
--   Show that $\frac{A}{A+B}+\frac{B}{B+C}+\frac{C}{C+A} < 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72039 : ∀ A B C : ℝ, (A / (A + B) + B / (B + C) + C / (C + A)) < 2   :=  by sorry

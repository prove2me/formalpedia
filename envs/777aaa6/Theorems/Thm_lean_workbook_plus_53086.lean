-- Prove2me | Theorems.Thm_lean_workbook_plus_53086
-- name    : lean_workbook_plus_53086
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/373ea547-651d-4479-ab47-47fea0b90f1e
-- statement:
--   What is the domain of the algebraic expression $f(x) = \sqrt{x}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53086 (f : ℝ → ℝ) (f_def : ∀ x, f x = Real.sqrt x) : ∀ x, x ≥ 0 → f x ∈ Set.univ   :=  by sorry

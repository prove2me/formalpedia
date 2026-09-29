-- Prove2me | Theorems.Thm_lean_workbook_plus_608
-- name    : lean_workbook_plus_608
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f33a9a60-d91b-4dae-af11-91bccd9ec731
-- statement:
--   Show that $k^n = (k-1)^n + (k^n - (k-1)^n) \cdot 1^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_608 : ∀ k n : ℕ, k^n = (k - 1)^n + (k^n - (k - 1)^n) * 1^n   :=  by sorry

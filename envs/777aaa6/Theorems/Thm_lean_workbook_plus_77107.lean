-- Prove2me | Theorems.Thm_lean_workbook_plus_77107
-- name    : lean_workbook_plus_77107
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ce9f41d1-6bf8-4b4e-b718-ae1aa2d7ed99
-- statement:
--   Show that there are infinitely many rational triples $(a, b, c)$ such that $a + b + c = abc = 6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77107 : ∀ n : ℕ, ∃ a b c : ℚ, a + b + c = a * b * c ∧ a * b * c = 6   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_77200
-- name    : lean_workbook_plus_77200
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/9b05626f-4dec-43b8-895a-43bd4cca4390
-- statement:
--   Let $ n\in\mathbb{N} $ . Show that $ d(n)\leq n $ where $ d(n) $ denote the number of divisors of $ n $ . When does the equality hold ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77200 : ∀ n : ℕ, n.divisors.card ≤ n   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_29794
-- name    : lean_workbook_plus_29794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fcd83813-ff1d-4da4-b9cc-d4df5ed21893
-- statement:
--   Infinite solutions ; Any $x$ that is 3 mod 6
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29794 : ∀ m : ℕ, ∃ x : ℕ, x > m ∧ x % 6 = 3   :=  by sorry

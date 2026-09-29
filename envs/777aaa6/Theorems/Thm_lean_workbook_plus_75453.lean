-- Prove2me | Theorems.Thm_lean_workbook_plus_75453
-- name    : lean_workbook_plus_75453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/33783e3d-8712-4f91-ac50-60dfdcc1fc5b
-- statement:
--   an even number has a remainder of $0$ when divided by $2$ , and an odd number has a remainder of $1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75453 : ∀ n : ℕ, (n % 2 = 0 ↔ Even n) ∧ (n % 2 = 1 ↔ Odd n)   :=  by sorry

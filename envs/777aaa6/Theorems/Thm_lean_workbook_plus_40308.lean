-- Prove2me | Theorems.Thm_lean_workbook_plus_40308
-- name    : lean_workbook_plus_40308
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/66ca340d-9efc-47d2-a8d5-959a7fb139e6
-- statement:
--   For all,n : (if n is odd ,then $ a_n = 0$ ) and ( if n is even,then $ a_n =\frac{n}{2}$ ).\nNow let us see if logic allows for that definition.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40308 (n : ℕ) (a : ℕ → ℕ) (h₁ : ∀ n, Odd n → a n = 0) (h₂ : ∀ n, Even n → a n = n / 2) : (∀ n, (Odd n ∨ Even n) → a n = 0 ∨ a n = n / 2)   :=  by sorry

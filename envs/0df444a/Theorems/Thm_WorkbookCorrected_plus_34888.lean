-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_34888
-- name    : WorkbookCorrected.plus_34888
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:55:24.199977+00:00
-- url     : https://prove2.me/theorems/16003e71-2d9e-4d61-b10b-8ac6625bba3c
-- title:
--   Closed form of a second-order linear recurrence
-- statement:
--   Let a₀ = 1, a₁ = 2, and aₙ₊₂ = 4aₙ₊₁+aₙ for every natural number n. Then aₙ = ((2+√5)ⁿ+(2−√5)ⁿ)/2 for every natural number n.
--
--   Formalization Note: Supplies the explicit closed form requested in the source; the original formalization merely asserted the existence of a function equal to the sequence.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_34888 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_34888; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_34888 (a : ℕ → ℝ) (h0 : a 0=1) (h1 : a 1=2)
    (h : ∀ n : ℕ, a (n+2)=4*a (n+1)+a n) :
    ∀ n : ℕ, a n=((2+Real.sqrt 5)^n+(2-Real.sqrt 5)^n)/2 := by sorry

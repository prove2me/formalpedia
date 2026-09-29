-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_40328
-- name    : WorkbookCorrected.plus_40328
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:01:22.411751+00:00
-- url     : https://prove2.me/theorems/11227e8e-308b-4cb5-845a-a4adeb46efae
-- title:
--   Integrality of a square-root recurrence via a Pell invariant
-- statement:
--   Let a₁ = 1 and aₙ₊₁ = 2aₙ+√(3aₙ²+1) for every integer n ≥ 1. Every term aₙ is an integer.
--
--   Formalization Note: Restores the source’s initial index 1 and its recurrence on positive indices. Equality to the integer floor expresses the stated integrality.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_40328 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_40328; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_40328 (a : ℕ → ℝ) (h1 : a 1=1)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=2*a n+Real.sqrt (3*a n^2+1)) :
    ∀ n : ℕ, 1 ≤ n → a n = (⌊a n⌋ : ℤ) := by sorry

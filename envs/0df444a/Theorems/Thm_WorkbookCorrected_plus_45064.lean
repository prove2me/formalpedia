-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45064
-- name    : WorkbookCorrected.plus_45064
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:10:53.995021+00:00
-- url     : https://prove2.me/theorems/e404cc6d-0481-43af-b6c3-4d642cd989b1
-- title:
--   A sequence characterized by its partial sums of cubes
-- statement:
--   Let a₁,a₂,… be positive real numbers. Suppose that for every positive integer n, a₁³+⋯+aₙ³ = (a₁+⋯+aₙ)². Then aₙ=n for every positive integer n.
--
--   Formalization Note: Restores the source’s positive indices in both partial sums and the conclusion; the original zero-index sums were inconsistent with its claimed formula.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45064 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_45064; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_45064 (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (h : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ Finset.range n, (a (i+1))^3)=(∑ i ∈ Finset.range n, a (i+1))^2) :
    ∀ n : ℕ, 1 ≤ n → a n=(n:ℝ) := by sorry

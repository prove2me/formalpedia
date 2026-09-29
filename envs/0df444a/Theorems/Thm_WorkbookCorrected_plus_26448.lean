-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_26448
-- name    : WorkbookCorrected.plus_26448
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:42:56.844847+00:00
-- url     : https://prove2.me/theorems/64d7ab04-1307-4b95-b8f9-f2939d5c951c
-- title:
--   Convergence of a quadratic square-root approximation
-- statement:
--   For c ∈ [0,1], let f₀ = 0 and fₙ₊₁ = fₙ + (c−fₙ²)/2 for every natural number n. Then fₙ converges to √c.
--
--   Formalization Note: Restores the complete epsilon/eventual quantifiers required for convergence in the natural source; the original formalization instead required arbitrary accuracy at a single index.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_26448 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_26448; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_26448 (c : ℝ) (hc : c ∈ Set.Icc 0 1) (f : ℕ → ℝ)
    (h0 : f 0 = 0) (h : ∀ n : ℕ, f (n+1)=f n+(c-(f n)^2)/2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f n-Real.sqrt c| < ε := by sorry

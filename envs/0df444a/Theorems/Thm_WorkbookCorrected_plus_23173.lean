-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_23173
-- name    : WorkbookCorrected.plus_23173
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:12:26.230378+00:00
-- url     : https://prove2.me/theorems/a25e5b21-6186-4344-8c6f-402cb2acd7cd
-- title:
--   Uniqueness of a solution to a real cube-root equation
-- statement:
--   The real equation
--   \[\sqrt[3]{x+7}-\sqrt[3]{2x-1}=\sqrt[3]{x}\]
--   has exactly one solution, $x=1$.
--
--   Formalization Note: The real cube roots are represented by their cubing equations, including negative radicands. The original formalization used natural-number division in fractional exponents. This corrected statement proves both that every solution is1 and that1 satisfies the equation.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_23173 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_23173; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_23173 : ∀ (x : ℝ),
    (∃ u v w : ℝ, u^3=x+7 ∧ v^3=2*x-1 ∧ w^3=x ∧ u-v=w) ↔ x=1 := by sorry

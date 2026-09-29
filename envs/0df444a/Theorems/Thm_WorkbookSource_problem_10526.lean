-- Prove2me | Theorems.Thm_WorkbookSource_problem_10526
-- name    : WorkbookSource.problem_10526
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:11.538583+00:00
-- url     : https://prove2.me/theorems/36d03cd2-8b6c-40d5-b589-ca7dd8b1d24d
-- title:
--   Rewriting a quotient of inverse powers
-- statement:
--   We know that $ \dfrac{a^{ - 1}b^{ - 1}}{a^{ - 3} - b^{ - 3}} = \dfrac{1}{\dfrac{1}{a^3} - \dfrac{1}{b^3}} \cdot \left( \dfrac{1}{ab}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10526` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10526; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_10526  (a b : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0)
  (h₂ : a ≠ b) :
  (a⁻¹ * b⁻¹) / (a⁻¹ ^ 3 - b⁻¹ ^ 3) = 1 / ((1 / a^3) - (1 / b^3)) * (1 / (a * b))  :=  by sorry

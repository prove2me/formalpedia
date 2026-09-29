-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_81229
-- name    : WorkbookSyntax.plus_81229
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:41:44.142951+00:00
-- url     : https://prove2.me/theorems/35cd94c1-3e3f-4848-8c93-b376f487486d
-- title:
--   Lean-Workbook Syntax 81229: The admissible auditorium seat counts sum to 615
-- statement:
--   The sum of all divisors of 2050 lying between 150 and 431 inclusive is 615.
--
--   Source: Lean-Workbook row `lean_workbook_plus_81229` (Apache-2.0), [original record](https://prove2.me/theorems/8175fd76-5b82-4332-895e-ac6a9e14566f). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_81229; immutable original Prove2Me node 8175fd76-5b82-4332-895e-ac6a9e14566f

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_81229 (n : ℕ) (h₁ : 150 ≤ n) (h₂ : n ≤ 431) (h₃ : n ∣ 2050) : ∑ k ∈ Finset.filter (λ x => x ∣ 2050) (Finset.Icc 150 431), k = 615   :=  by sorry

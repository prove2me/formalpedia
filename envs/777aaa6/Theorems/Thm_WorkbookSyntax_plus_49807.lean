-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_49807
-- name    : WorkbookSyntax.plus_49807
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:06:41.844694+00:00
-- url     : https://prove2.me/theorems/8f057646-b535-4657-b7d1-8fcb7e2135a9
-- title:
--   Lean-Workbook Syntax 49807: A product bounds one plus the sum
-- statement:
--   For a finite set $A$ of nonnegative real numbers, $1+\sum_{x\in A}x\le\prod_{x\in A}(1+x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_49807` (Apache-2.0), [original record](https://prove2.me/theorems/2ae07208-cbb5-4283-a3fa-5b88a333b6d2). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_49807; immutable original Prove2Me node 2ae07208-cbb5-4283-a3fa-5b88a333b6d2

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

theorem WorkbookSyntax.plus_49807 (A : Finset ℝ) (hA : ∀ x ∈ A, 0 ≤ x) :
  1 + ∑ x ∈ A, x ≤ ∏ x ∈ A, (1 + x)   :=  by sorry

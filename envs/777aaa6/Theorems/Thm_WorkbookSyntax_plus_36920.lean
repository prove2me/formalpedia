-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_36920
-- name    : WorkbookSyntax.plus_36920
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:22:07.728516+00:00
-- url     : https://prove2.me/theorems/7a81aa57-6a46-45bb-85f6-93e8f6e845b9
-- title:
--   Lean-Workbook Syntax 36920: Counting the positive divisors of 72
-- statement:
--   The integer $72$ has exactly $12$ positive divisors.
--
--   Source: Lean-Workbook row `lean_workbook_plus_36920` (Apache-2.0), [original record](https://prove2.me/theorems/67dacb5b-c9f7-489e-9289-8ef168eb7b2f). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_36920; immutable original Prove2Me node 67dacb5b-c9f7-489e-9289-8ef168eb7b2f

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Divisors

theorem WorkbookSyntax.plus_36920 :
  (∑ k ∈ (Nat.divisors 72), 1) = 12   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_34532
-- name    : WorkbookSyntax.plus_34532
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:21:48.766125+00:00
-- url     : https://prove2.me/theorems/a98746cc-537e-4267-b091-5de77d0664f0
-- title:
--   Lean-Workbook Syntax 34532: Sum of the first n natural numbers
-- statement:
--   For every natural $n$, $\sum_{i=0}^{n}i=n(n+1)/2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34532` (Apache-2.0), [original record](https://prove2.me/theorems/7bcd74e6-9a7e-4f6b-8a74-597b1977f751). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34532; immutable original Prove2Me node 7bcd74e6-9a7e-4f6b-8a74-597b1977f751

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_34532 (n : ℕ) : (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) / 2   :=  by sorry

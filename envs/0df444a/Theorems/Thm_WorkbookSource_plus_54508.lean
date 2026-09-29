-- Prove2me | Theorems.Thm_WorkbookSource_plus_54508
-- name    : WorkbookSource.plus_54508
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T16:12:07.949794+00:00
-- url     : https://prove2.me/theorems/053692b3-0ff5-4282-abbf-b88fc6d8692b
-- title:
--   Exact reciprocal sum from a bilinear recurrence
-- statement:
--   Let $a_0=3$ and suppose the real sequence satisfies
--   $$(3-a_{n+1})(6+a_n)=18\qquad(n\geq0).$$
--   Then
--   $$\sum_{k=0}^{12}\frac1{a_k}=\frac{16369}{3}.$$
--   The statement gives the exact reciprocal sum for the specified nonlinear recurrence.
--
--   Formalization Note: The source proposition is retained; obsolete summation notation is updated for Lean 4.33.1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_54508; Apache-2.0

import Mathlib
open scoped BigOperators

theorem WorkbookSource.plus_54508 (a : ℕ → ℝ) (a0 : a 0 = 3) (a_rec : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) : ∑ k ∈ Finset.range 13, (1 / a k) = 16369 / 3   :=  by sorry

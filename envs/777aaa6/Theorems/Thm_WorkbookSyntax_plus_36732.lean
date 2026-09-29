-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_36732
-- name    : WorkbookSyntax.plus_36732
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:21:53.535596+00:00
-- url     : https://prove2.me/theorems/27d7ef08-502c-40ff-865a-eac316e0923e
-- title:
--   Lean-Workbook Syntax 36732: Solving a finite arithmetic-sum equation
-- statement:
--   If a natural number $n$ satisfies $\sum_{k=0}^{6}(n+k)=3(n+6)+3$, then $n=0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_36732` (Apache-2.0), [original record](https://prove2.me/theorems/7a434360-68ff-4776-8a32-fc0429424aa0). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_36732; immutable original Prove2Me node 7a434360-68ff-4776-8a32-fc0429424aa0

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_36732  (n : ℕ)
  (h₀ : ∑ k ∈ Finset.Icc 0 6, (n + k) = 3 * (n + 6) + 3) :
  n = 0   :=  by sorry

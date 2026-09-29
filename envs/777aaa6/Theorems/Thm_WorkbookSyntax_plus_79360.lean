-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_79360
-- name    : WorkbookSyntax.plus_79360
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:41:55.500985+00:00
-- url     : https://prove2.me/theorems/66128a40-7bdf-4766-9df1-79d4db2fffbd
-- title:
--   Lean-Workbook Syntax 79360: The finite sum of powers of two
-- statement:
--   For every natural $n$, $\sum_{i=0}^{n-1}2^i=2^n-1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_79360` (Apache-2.0), [original record](https://prove2.me/theorems/d4d0954b-ba6c-4d5a-85c9-0dd03d9a6165). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_79360; immutable original Prove2Me node d4d0954b-ba6c-4d5a-85c9-0dd03d9a6165

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_79360 : ∀ n : ℕ, ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1   :=  by sorry

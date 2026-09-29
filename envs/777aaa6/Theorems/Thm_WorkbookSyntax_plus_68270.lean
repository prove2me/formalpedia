-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_68270
-- name    : WorkbookSyntax.plus_68270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:53.225927+00:00
-- url     : https://prove2.me/theorems/10b8f497-2892-44b0-9acd-2f0b655bdfbc
-- title:
--   Lean-Workbook Syntax 68270: The sum of the first four positive integers
-- statement:
--   $\sum_{k=1}^{4}k=10$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_68270` (Apache-2.0), [original record](https://prove2.me/theorems/43d407f2-22af-465d-87c0-dd4acf6274e8). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_68270; immutable original Prove2Me node 43d407f2-22af-465d-87c0-dd4acf6274e8

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_68270 : ∑ k ∈ Finset.Icc 1 4, k = 10   :=  by sorry

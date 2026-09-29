-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_77340
-- name    : WorkbookSyntax.plus_77340
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:41:47.092+00:00
-- url     : https://prove2.me/theorems/c050c88c-bdb5-4603-9ece-1a3643b738ea
-- title:
--   Lean-Workbook Syntax 77340: A telescoping sum of powers of five
-- statement:
--   $\sum_{i=1}^{100}(5^i-5^{i-1})=5^{100}-1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_77340` (Apache-2.0), [original record](https://prove2.me/theorems/341ebc4e-6c40-4165-abfb-60b29746e6e2). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_77340; immutable original Prove2Me node 341ebc4e-6c40-4165-abfb-60b29746e6e2

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_77340 : ∑ i ∈ Finset.Icc 1 100, (5^i - 5^(i-1)) = 5^100 - 1   :=  by sorry

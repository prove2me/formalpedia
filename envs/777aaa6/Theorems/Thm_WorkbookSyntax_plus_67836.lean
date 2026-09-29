-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_67836
-- name    : WorkbookSyntax.plus_67836
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:56.089109+00:00
-- url     : https://prove2.me/theorems/5a6d3f46-b457-4154-9e39-ea62931d01e4
-- title:
--   Lean-Workbook Syntax 67836: A finite sum of gcd values
-- statement:
--   $\sum_{i=1}^{2019}\gcd(i,2019-i)=6725$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_67836` (Apache-2.0), [original record](https://prove2.me/theorems/4b0ea5bd-bcfb-45ac-8bed-12b0046e9e67). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_67836; immutable original Prove2Me node 4b0ea5bd-bcfb-45ac-8bed-12b0046e9e67

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_67836 : ∑ i ∈ Finset.Icc 1 2019, Nat.gcd i (2019 - i) = 6725   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_70836
-- name    : WorkbookSyntax.plus_70836
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:29.417978+00:00
-- url     : https://prove2.me/theorems/ca145962-5927-4787-ac41-35ba29f7bc39
-- title:
--   Lean-Workbook Syntax 70836: A fourth-power bound for a sum of cubes
-- statement:
--   For every natural $n$, $\sum_{i=0}^{n}i^3\le n^4$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_70836` (Apache-2.0), [original record](https://prove2.me/theorems/05b6dea1-9caf-4bab-8c5a-f5f8da278995). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_70836; immutable original Prove2Me node 05b6dea1-9caf-4bab-8c5a-f5f8da278995

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_70836 (n : ℕ) : ∑ i ∈ Finset.range (n+1), i^3 ≤ n^4   :=  by sorry

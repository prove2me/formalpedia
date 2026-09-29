-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_47065
-- name    : WorkbookSyntax.plus_47065
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:06:34.774811+00:00
-- url     : https://prove2.me/theorems/59bf4d89-2485-4a16-aa6a-f3a4647277f8
-- title:
--   Lean-Workbook Syntax 47065: A finite geometric sum is below the next power
-- statement:
--   For natural $p>1$ and $n\ge0$, $\sum_{k=0}^{n-1}p^k<p^n$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_47065` (Apache-2.0), [original record](https://prove2.me/theorems/9f0d0283-2ed5-424a-8ff3-304cf80cf7db). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_47065; immutable original Prove2Me node 9f0d0283-2ed5-424a-8ff3-304cf80cf7db

import Mathlib.Algebra.Order.BigOperators.Group.Finset

theorem WorkbookSyntax.plus_47065 (p : ℕ) (hp : 1 < p) (n : ℕ) : ∑ k ∈ Finset.range n, p^k < p^n   :=  by sorry

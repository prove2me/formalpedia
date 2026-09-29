-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_69605
-- name    : WorkbookSyntax.plus_69605
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:09:06.686058+00:00
-- url     : https://prove2.me/theorems/ed936564-9541-48af-b910-258e17bff2b8
-- title:
--   Lean-Workbook Syntax 69605: The sum of the first n squares
-- statement:
--   For every natural number $n$, $\sum_{i=0}^{n}i^2=n(n+1)(2n+1)/6$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_69605` (Apache-2.0), [original record](https://prove2.me/theorems/89d0d3c6-0d14-49e9-94ca-02a744b8fd42). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_69605; immutable original Prove2Me node 89d0d3c6-0d14-49e9-94ca-02a744b8fd42

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_69605 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry

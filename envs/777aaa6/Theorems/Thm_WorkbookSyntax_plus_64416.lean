-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_64416
-- name    : WorkbookSyntax.plus_64416
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:20:04.631865+00:00
-- url     : https://prove2.me/theorems/c2760d88-35d8-4d8b-a327-4a3b55c8b57d
-- title:
--   Lean-Workbook Syntax 64416: Half of an odd binomial row
-- statement:
--   If $p(x)=\sum_{i=0}^{1007}\binom{x}{i}$ for natural $x$, then $p(2015)=2^{2014}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_64416` (Apache-2.0), [original record](https://prove2.me/theorems/21698a2b-044e-44d3-87a1-6c62746dd3f3). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_64416; immutable original Prove2Me node 21698a2b-044e-44d3-87a1-6c62746dd3f3

import Mathlib.Data.Nat.Choose.Sum

theorem WorkbookSyntax.plus_64416 (p : ℕ → ℕ) (hp : ∀ x, p x = ∑ i ∈ Finset.range 1008, Nat.choose x i) : p 2015 = 2^2014   :=  by sorry

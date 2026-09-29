-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_34585
-- name    : WorkbookSyntax.plus_34585
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:22:09.509399+00:00
-- url     : https://prove2.me/theorems/625fc9dc-9dfd-45b1-a719-956c63b170e8
-- title:
--   Lean-Workbook Syntax 34585: A partial alternating binomial sum
-- statement:
--   For natural $n,m$, $\sum_{k=0}^{m}(-1)^k\binom{2n+1}{k}=(-1)^m\binom{2n}{m}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34585` (Apache-2.0), [original record](https://prove2.me/theorems/c1156290-7612-4460-a039-cb8199537f5b). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34585; immutable original Prove2Me node c1156290-7612-4460-a039-cb8199537f5b

import Mathlib.Data.Nat.Choose.Sum

theorem WorkbookSyntax.plus_34585 (n m : ℕ) : ∑ k ∈ Finset.range (m+1), (-1 : ℤ)^k * (2*n+1).choose k = (-1)^m * (2*n).choose m   :=  by sorry

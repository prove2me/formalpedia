-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_58729
-- name    : WorkbookSyntax.plus_58729
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:10:34.628042+00:00
-- url     : https://prove2.me/theorems/44b29542-ffa6-4369-bd7c-6cf7ba9f31dc
-- title:
--   Lean-Workbook Syntax 58729: An alternating even-index binomial sum
-- statement:
--   $\sum_{k=0}^{49}(-1)^k\binom{99}{2k}=-2^{49}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_58729` (Apache-2.0), [original record](https://prove2.me/theorems/2bdc2b86-e76c-46f9-a2f6-05046072a602). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_58729; immutable original Prove2Me node 2bdc2b86-e76c-46f9-a2f6-05046072a602

import Mathlib.Data.Nat.Choose.Sum

theorem WorkbookSyntax.plus_58729 (n : ℕ) : ∑ k ∈ Finset.range (49+1), (-1 : ℤ)^k * (99).choose (2 * k) = (-1 : ℤ)^49 * 2^49   :=  by sorry

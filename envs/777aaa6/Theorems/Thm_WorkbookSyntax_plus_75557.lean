-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_75557
-- name    : WorkbookSyntax.plus_75557
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:28.679277+00:00
-- url     : https://prove2.me/theorems/f0746d03-a631-4997-9b83-966c744205f4
-- title:
--   Lean-Workbook Syntax 75557: Six equals the sum of its proper divisors
-- statement:
--   The positive proper divisors of $6$ sum to $6$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_75557` (Apache-2.0), [original record](https://prove2.me/theorems/cf63f91e-d215-4fb6-8854-b8ef0c919f11). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_75557; immutable original Prove2Me node cf63f91e-d215-4fb6-8854-b8ef0c919f11

import Mathlib.NumberTheory.Divisors

theorem WorkbookSyntax.plus_75557 :
  ∑ k ∈ (Nat.properDivisors 6), k = 6   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_51761
-- name    : WorkbookSyntax.plus_51761
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:06:47.67098+00:00
-- url     : https://prove2.me/theorems/f2ba5dcc-33df-4d8a-a9b9-468345abef16
-- title:
--   Lean-Workbook Syntax 51761: Counting the positive divisors of 576
-- statement:
--   The integer $576$ has exactly $21$ positive divisors.
--
--   Source: Lean-Workbook row `lean_workbook_plus_51761` (Apache-2.0), [original record](https://prove2.me/theorems/fd667cd0-6a7e-4473-b4e6-4b1c3624b38d). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_51761; immutable original Prove2Me node fd667cd0-6a7e-4473-b4e6-4b1c3624b38d

import Mathlib.NumberTheory.Divisors

theorem WorkbookSyntax.plus_51761 :
  (∑ k ∈ (Nat.divisors 576), 1) = 21   :=  by sorry

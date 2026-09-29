-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_42311
-- name    : WorkbookSyntax.plus_42311
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:23:40.713384+00:00
-- url     : https://prove2.me/theorems/1297e556-6591-4cbf-8cf4-52227b6da2ed
-- title:
--   The sum of totients over the divisors of an integer
-- statement:
--   For every natural number n, the sum of φ(d) over the positive divisors d of n equals n.
--
--   Notation repair: Replace the obsolete finite-sum binder in with ∈, and restore Nat and its totient notation scope. The complete proposition, divisors, summand, and quantifier are preserved.
--
--   Source: Lean-Workbook record `lean_workbook_plus_42311` (Apache-2.0). [Original declaration](https://prove2.me/theorems/af31cf80-5014-47c3-bcd2-08b6e8f51721).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_42311; Apache-2.0

import Mathlib
open Nat
open scoped Nat

theorem WorkbookSyntax.plus_42311 (n : ℕ) : ∑ k ∈ divisors n, φ k = n   :=  by sorry

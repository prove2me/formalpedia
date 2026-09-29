-- Prove2me | Theorems.Thm_WorkbookRestored_plus_51287
-- name    : WorkbookRestored.plus_51287
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:50.514721+00:00
-- url     : https://prove2.me/theorems/4fee584f-2cb0-4b5a-ac01-13ee4b682259
-- title:
--   Divisibility of Fibonacci numbers
-- statement:
--   For natural numbers $n,m$, if $n\mid m$, then $F_n\mid F_m$, where $F_n$ denotes the Fibonacci sequence with $F_0=0$, $F_1=1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_51287` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/b7a243e0-12d4-4217-8163-0dda4f96ac15); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_51287; immutable original Prove2Me node b7a243e0-12d4-4217-8163-0dda4f96ac15

import Mathlib.Data.Nat.Fib.Basic
open Nat

theorem WorkbookRestored.plus_51287 (n m : ℕ) (hn : n ∣ m) : fib n ∣ fib m   :=  by sorry

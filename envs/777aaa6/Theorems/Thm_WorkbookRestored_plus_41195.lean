-- Prove2me | Theorems.Thm_WorkbookRestored_plus_41195
-- name    : WorkbookRestored.plus_41195
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:22.915586+00:00
-- url     : https://prove2.me/theorems/6f7e65e7-6c25-4052-bb71-6c69b92795e2
-- title:
--   The greatest common divisor of two Fibonacci numbers
-- statement:
--   For natural numbers $n,m$, $\gcd(F_n,F_m)=F_{\gcd(n,m)}$, where $F_0=0$, $F_1=1$ and $F_{r+2}=F_r+F_{r+1}$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/62fdbf73-c359-4363-ad01-cfb6184d1302), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_41195` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_41195; original Prove2Me node 62fdbf73-c359-4363-ad01-cfb6184d1302; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
open Nat

theorem WorkbookRestored.plus_41195 (n m : ℕ) : Nat.gcd (Nat.fib n) (Nat.fib m) = Nat.fib (Nat.gcd n m)   :=  by sorry

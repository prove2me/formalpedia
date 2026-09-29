-- Prove2me | Theorems.Thm_WorkbookRestored_plus_78499
-- name    : WorkbookRestored.plus_78499
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:41:54.092984+00:00
-- url     : https://prove2.me/theorems/b3fc8ec1-e651-448c-ba66-fa547c81a37f
-- title:
--   Lean-Workbook Plus 78499: Last digits of the first five factorials
-- statement:
--   Let $f(n)=n-10\lfloor n/10\rfloor$ for natural $n$. Then $f(0!)+f(1!)+f(2!)+f(3!)+f(4!)=14$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_78499` (Apache-2.0), [original record](https://prove2.me/theorems/0e8f509e-47eb-4e5f-b0e3-e138a03ce7a2). This repair only restores required imports and namespaces; the mathematical declaration is unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_78499; immutable original Prove2Me node 0e8f509e-47eb-4e5f-b0e3-e138a03ce7a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Semiring
open Nat

theorem WorkbookRestored.plus_78499 (f : ℕ → ℕ) (f_def : ∀ n, f n = n - 10 * Nat.floor (n / 10)) : f 0! + f 1! + f 2! + f 3! + f 4! = 14   :=  by sorry

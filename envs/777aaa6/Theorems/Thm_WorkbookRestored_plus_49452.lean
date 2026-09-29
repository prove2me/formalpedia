-- Prove2me | Theorems.Thm_WorkbookRestored_plus_49452
-- name    : WorkbookRestored.plus_49452
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:43.231968+00:00
-- url     : https://prove2.me/theorems/468f6413-ba5d-44a4-8b56-f9e2c399ac55
-- title:
--   The fourteenth Fibonacci number
-- statement:
--   The fourteenth Fibonacci number is $F_{14}=377$, with $F_0=0$, $F_1=1$ and $F_{n+2}=F_n+F_{n+1}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_49452` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/48463b56-7ef9-4600-96ec-2ef8197e33ba); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_49452; immutable original Prove2Me node 48463b56-7ef9-4600-96ec-2ef8197e33ba

import Mathlib.Data.Nat.Fib.Basic
open Nat

theorem WorkbookRestored.plus_49452 : fib 14 = 377   :=  by sorry

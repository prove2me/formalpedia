-- Prove2me | Theorems.Thm_WorkbookRestored_plus_9802
-- name    : WorkbookRestored.plus_9802
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:41.428915+00:00
-- url     : https://prove2.me/theorems/8b98d532-ce67-47a7-9333-6eed07d427eb
-- title:
--   A sum of two consecutive Fibonacci squares
-- statement:
--   For the Fibonacci sequence with $F_0=0$ and $F_1=1$, every natural number $n$ satisfies $$F_n^2+F_{n+1}^2=F_{2n+1}.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/1e0209bc-c754-4f67-8176-ec0ed721360b), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_9802` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_9802; original Prove2Me node 1e0209bc-c754-4f67-8176-ec0ed721360b; Apache-2.0

import Mathlib.Data.Nat.Fib.Basic
open Nat

theorem WorkbookRestored.plus_9802 (n : ℕ) : fib n ^ 2 + fib (n + 1) ^ 2 = fib (2 * n + 1)   :=  by sorry

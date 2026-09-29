-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14129
-- name    : WorkbookRestored.plus_14129
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:13:56.808372+00:00
-- url     : https://prove2.me/theorems/891f60d7-a745-410c-b4ac-d73fbc481dfa
-- title:
--   The Fibonacci recurrence at consecutive indices
-- statement:
--   For every natural $k$, $F_k+F_{k+1}=F_{k+2}$, with $F_0=0$ and $F_1=1$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/28a2d7c7-3eb5-45fd-920d-004a14534470), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_14129` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14129; original Prove2Me node 28a2d7c7-3eb5-45fd-920d-004a14534470; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
open Nat

theorem WorkbookRestored.plus_14129 : ∀ k : ℕ, fib k + fib (k + 1) = fib (k + 2)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_61921
-- name    : WorkbookSyntax.plus_61921
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:19:59.289692+00:00
-- url     : https://prove2.me/theorems/98d82664-d3cc-41fc-b014-d9a3a174f128
-- title:
--   Lean-Workbook Syntax 61921: A sum of squared Fibonacci numbers
-- statement:
--   For every natural $n$, $\sum_{k=0}^{n}F_k^2=F_nF_{n+1}$, where $F_0=0,F_1=1$ and $F_{n+2}=F_{n+1}+F_n$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_61921` (Apache-2.0), [original record](https://prove2.me/theorems/54e71ffc-f3ec-44b5-beb4-1556d90b15ba). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_61921; immutable original Prove2Me node 54e71ffc-f3ec-44b5-beb4-1556d90b15ba

import Mathlib.Data.Nat.Fib.Basic
open Nat

theorem WorkbookSyntax.plus_61921 (n : ℕ) : ∑ k ∈ Finset.range (n+1), fib k ^ 2 = fib n * fib (n + 1)   :=  by sorry

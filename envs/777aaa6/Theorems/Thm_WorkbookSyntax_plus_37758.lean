-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_37758
-- name    : WorkbookSyntax.plus_37758
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:21:58.519283+00:00
-- url     : https://prove2.me/theorems/c08144b3-6282-4c87-862d-55ad471965f5
-- title:
--   Lean-Workbook Syntax 37758: Product of factorials divides factorial of the sum
-- statement:
--   For any finite list of natural numbers $x_0,\ldots,x_{k-1}$, $\prod_{i=0}^{k-1}x_i!\mid\bigl(\sum_{i=0}^{k-1}x_i\bigr)!$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_37758` (Apache-2.0), [original record](https://prove2.me/theorems/9f0f5014-a192-43a2-b635-0055cd49d022). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_37758; immutable original Prove2Me node 9f0f5014-a192-43a2-b635-0055cd49d022

import Mathlib.Data.Nat.Factorial.BigOperators
open Nat

theorem WorkbookSyntax.plus_37758 (x : ℕ → ℕ) (k : ℕ) :
  ∏ i ∈ Finset.range k, (x i)! ∣ (∑ i ∈ Finset.range k, x i)!   :=  by sorry

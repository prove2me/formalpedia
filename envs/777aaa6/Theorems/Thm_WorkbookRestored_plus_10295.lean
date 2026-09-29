-- Prove2me | Theorems.Thm_WorkbookRestored_plus_10295
-- name    : WorkbookRestored.plus_10295
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:40.646605+00:00
-- url     : https://prove2.me/theorems/1219fe52-5739-44b0-8393-f0603f522e10
-- title:
--   Complementary choices in a shifted set size
-- statement:
--   For natural numbers $n,k$, $$\binom{n-1+k}{n-1}=\binom{n-1+k}k.$$ Here $n-1$ uses natural subtraction, so it is zero when $n=0$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/0460bf51-2b1a-45d0-af2b-e2c03a594c20), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_10295` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_10295; original Prove2Me node 0460bf51-2b1a-45d0-af2b-e2c03a594c20; Apache-2.0

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_10295 (n k : ℕ) : choose (n - 1 + k) (n - 1) = choose (n - 1 + k) k   :=  by sorry

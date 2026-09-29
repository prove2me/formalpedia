-- Prove2me | Theorems.Thm_WorkbookRestored_plus_3121
-- name    : WorkbookRestored.plus_3121
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:24.944462+00:00
-- url     : https://prove2.me/theorems/5abc017b-912d-4952-8d94-47140f40c76e
-- title:
--   Counting ordered pairs of distinct elements
-- statement:
--   For every natural number $n$, $$n(n-1)=2\binom n2.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/d8bf9e24-d293-4827-80c9-1d69e9d45a65), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_3121` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_3121; original Prove2Me node d8bf9e24-d293-4827-80c9-1d69e9d45a65; Apache-2.0

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_3121 (n : ℕ) : n * (n - 1) = 2 * choose n 2   :=  by sorry

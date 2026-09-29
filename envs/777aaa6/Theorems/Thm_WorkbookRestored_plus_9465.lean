-- Prove2me | Theorems.Thm_WorkbookRestored_plus_9465
-- name    : WorkbookRestored.plus_9465
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:31.663437+00:00
-- url     : https://prove2.me/theorems/2a3c47ce-cac6-4b4b-9541-e375525063f5
-- title:
--   Applying Pascal’s recurrence twice
-- statement:
--   For every natural number $n$, $$\binom{n+2}4=\binom n2+2\binom n3+\binom n4.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/2919d552-4766-4c5f-b650-f0bbec90ff33), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_9465` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_9465; original Prove2Me node 2919d552-4766-4c5f-b650-f0bbec90ff33; Apache-2.0

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_9465 (n : ℕ) : choose (n + 2) 4 = choose n 2 + 2 * choose n 3 + choose n 4   :=  by sorry

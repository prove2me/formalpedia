-- Prove2me | Theorems.Thm_WorkbookRestored_plus_10203
-- name    : WorkbookRestored.plus_10203
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:36.00071+00:00
-- url     : https://prove2.me/theorems/945a288b-e2da-40c1-a754-b994f190ad06
-- title:
--   Pascal’s recurrence for pairs and triples
-- statement:
--   For every natural number $r$, $$\binom{r+1}2+\binom{r+1}3=\binom{r+2}3.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/94ba9c8f-ec8f-4fc5-8365-2adc7a7f0d44), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_10203` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_10203; original Prove2Me node 94ba9c8f-ec8f-4fc5-8365-2adc7a7f0d44; Apache-2.0

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_10203 (r : ℕ) : choose (r + 1) 2 + choose (r + 1) 3 = choose (r + 2) 3   :=  by sorry

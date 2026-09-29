-- Prove2me | Theorems.Thm_WorkbookRestored_plus_40829
-- name    : WorkbookRestored.plus_40829
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:24.311631+00:00
-- url     : https://prove2.me/theorems/72f82c08-7e57-4e3c-95ef-66b36c4d1b00
-- title:
--   An out-of-range odd binomial coefficient vanishes
-- statement:
--   For natural $n,j$ with $2j+1>n$, $\binom n{2j+1}=0$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/456a017f-aa8d-4451-88dd-99ba7457eb39), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_40829` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_40829; original Prove2Me node 456a017f-aa8d-4451-88dd-99ba7457eb39; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_40829 (n j : ℕ) (h₁ : 2 * j + 1 > n) : choose n (2 * j + 1) = 0   :=  by sorry

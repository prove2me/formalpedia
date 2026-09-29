-- Prove2me | Theorems.Thm_WorkbookRestored_plus_15734
-- name    : WorkbookRestored.plus_15734
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:02.97772+00:00
-- url     : https://prove2.me/theorems/2bc15b38-d5df-4718-8021-f8d92d2e552b
-- title:
--   A number and its decimal digit sum agree modulo nine
-- statement:
--   For every natural $n$, the sum of its decimal digits is congruent to $n$ modulo nine.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/f1b17e4f-47a1-4dbf-b625-b740f15e04b5), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_15734` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_15734; original Prove2Me node f1b17e4f-47a1-4dbf-b625-b740f15e04b5; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Digits.Lemmas
open Nat

theorem WorkbookRestored.plus_15734 (n : ℕ) : (Nat.digits 10 n).sum % 9 = n % 9   :=  by sorry

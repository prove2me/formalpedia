-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14185
-- name    : WorkbookRestored.plus_14185
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:14.967526+00:00
-- url     : https://prove2.me/theorems/9867c90d-bfe8-44ff-a3db-c4dfd950f12a
-- title:
--   Choosing two elements from two equal blocks
-- statement:
--   For every natural $n$, $\binom{2n}{2}=2\binom n2+n^2$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/c1b512d3-75a7-4d26-99f7-b5599b42c3d3), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_14185` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14185; original Prove2Me node c1b512d3-75a7-4d26-99f7-b5599b42c3d3; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
open Nat

theorem WorkbookRestored.plus_14185 (n : ℕ) : choose (2 * n) 2 = 2 * choose n 2 + n^2   :=  by sorry

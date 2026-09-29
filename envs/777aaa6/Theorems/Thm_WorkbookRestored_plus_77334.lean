-- Prove2me | Theorems.Thm_WorkbookRestored_plus_77334
-- name    : WorkbookRestored.plus_77334
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:41:34.663909+00:00
-- url     : https://prove2.me/theorems/ef95c347-3ce1-4d29-bcd9-06b78e4f47d3
-- title:
--   Lean-Workbook Plus 77334: Euler’s totient at fifteen
-- statement:
--   $\varphi(15)=8$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_77334` (Apache-2.0), [original record](https://prove2.me/theorems/ce767a9d-3bfe-496d-8797-95a0d3fc1b7f). This repair only restores required imports and namespaces; the mathematical declaration is unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_77334; immutable original Prove2Me node ce767a9d-3bfe-496d-8797-95a0d3fc1b7f

import Mathlib.Data.Nat.Totient
open Nat

theorem WorkbookRestored.plus_77334 (n : ℕ) (h : n = 15) : φ n = 8   :=  by sorry

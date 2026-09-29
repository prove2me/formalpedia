-- Prove2me | Theorems.Thm_WorkbookRestored_plus_72890
-- name    : WorkbookRestored.plus_72890
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:35.187961+00:00
-- url     : https://prove2.me/theorems/1cba3a84-2b0a-4323-8325-3477d79d5377
-- title:
--   Lean-Workbook Plus 72890: Fifteen factorial is divisible by one thousand
-- statement:
--   $15!\equiv0\pmod{1000}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_72890` (Apache-2.0), [original record](https://prove2.me/theorems/9a2d6cba-e7fa-4c1b-888b-12ba07253159). This repair only restores required imports and namespaces; the mathematical declaration is unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_72890; immutable original Prove2Me node 9a2d6cba-e7fa-4c1b-888b-12ba07253159

import Mathlib.Data.Nat.Factorial.Basic
open Nat

theorem WorkbookRestored.plus_72890 : 15! % 1000 = 0   :=  by sorry

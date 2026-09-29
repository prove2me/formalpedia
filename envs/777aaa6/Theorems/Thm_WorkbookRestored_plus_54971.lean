-- Prove2me | Theorems.Thm_WorkbookRestored_plus_54971
-- name    : WorkbookRestored.plus_54971
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:46:19.673181+00:00
-- url     : https://prove2.me/theorems/e336d182-b25a-42d5-a33d-7c15b358a45c
-- title:
--   Lean-Workbook Plus 54971: Factorial congruence modulo 437
-- statement:
--   $18!\equiv -1\pmod{437}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_54971` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5f255e6f-1041-4674-a712-82c72b2c6b50); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_54971; immutable original Prove2Me node 5f255e6f-1041-4674-a712-82c72b2c6b50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.ModEq
open Nat

theorem WorkbookRestored.plus_54971 : 18! ≡ -1 [ZMOD 437]   :=  by sorry

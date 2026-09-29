-- Prove2me | Theorems.Thm_WorkbookRestored_plus_34252
-- name    : WorkbookRestored.plus_34252
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:33:31.72185+00:00
-- url     : https://prove2.me/theorems/478a8362-b16c-4e3e-b8fe-836773073b2f
-- title:
--   Lean-Workbook Plus 34252: Trigonometric identity
-- statement:
--   **Lean-Workbook Plus 34252: Factorial congruence**
--
--   $9!\equiv-1\pmod{71}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34252` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/ba697768-e761-45c5-aa21-1d0478baffa5); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34252; immutable original Prove2Me node ba697768-e761-45c5-aa21-1d0478baffa5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.ModEq
open Nat

theorem WorkbookRestored.plus_34252 : 9! ≡ -1 [ZMOD 71]   :=  by sorry

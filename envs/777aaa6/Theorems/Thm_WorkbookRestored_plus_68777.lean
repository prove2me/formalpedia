-- Prove2me | Theorems.Thm_WorkbookRestored_plus_68777
-- name    : WorkbookRestored.plus_68777
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:45.457995+00:00
-- url     : https://prove2.me/theorems/1ef2b752-2261-462c-a35e-26bb09a48ea0
-- title:
--   Lean-Workbook Plus 68777: Totient of 462
-- statement:
--   $\varphi(462)=120$. Thus 120 integers from 1 through 462 are coprime to 462.
--
--   Source: Lean-Workbook row `lean_workbook_plus_68777` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a93df8b9-2e87-4bb7-a25f-029eb34d24d8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_68777; immutable original Prove2Me node a93df8b9-2e87-4bb7-a25f-029eb34d24d8

import Mathlib.Data.Nat.Totient

theorem WorkbookRestored.plus_68777 :
  Nat.totient 462 = 120   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_61458
-- name    : WorkbookRestored.plus_61458
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:58:17.597029+00:00
-- url     : https://prove2.me/theorems/d0fab0e4-ab74-44ff-ae40-0ff0826a3b72
-- title:
--   Lean-Workbook Plus 61458: Totient preserves divisibility
-- statement:
--   For natural numbers $d,n$, if $d\mid n$ then $\varphi(d)\mid\varphi(n)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_61458` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6210b3f3-9f34-4842-b00e-bed319877091); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_61458; immutable original Prove2Me node 6210b3f3-9f34-4842-b00e-bed319877091

import Mathlib.Data.Nat.Totient
open Nat

theorem WorkbookRestored.plus_61458 {d n : ℕ} (h : d ∣ n) : totient d ∣ totient n   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_44381
-- name    : WorkbookRestored.plus_44381
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:58.146507+00:00
-- url     : https://prove2.me/theorems/8ebbfd31-eb9e-45e2-942d-0eb083efd602
-- title:
--   Lean-Workbook Plus 44381: Logarithmic identity
-- statement:
--   If $x=2^{\log_6 18}3^{\log_6 3}$, then $x=6$, with real powers.
--
--   Source: Lean-Workbook row `lean_workbook_plus_44381` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/87219995-cee1-410f-812c-3c28b289155c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_44381; immutable original Prove2Me node 87219995-cee1-410f-812c-3c28b289155c

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_44381 (x : ℝ) (hx : x = 2^Real.logb 6 18 * 3^Real.logb 6 3) : x = 6   :=  by sorry

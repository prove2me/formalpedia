-- Prove2me | Theorems.Thm_WorkbookRestored_plus_11509
-- name    : WorkbookRestored.plus_11509
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:21.602398+00:00
-- url     : https://prove2.me/theorems/806b88dd-9890-420b-a8e4-1e94ed14af74
-- title:
--   Lean-Workbook Plus 11509: Logarithmic inequality
-- statement:
--   Prove for every $x>0$ : $ln(x^3-2x^2+x+1)\geq 0$
--
--   Source: Lean-Workbook row `lean_workbook_plus_11509` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4dc38eb9-9cb2-40ee-80fc-407c7e8c35d7); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_11509; immutable original Prove2Me node 4dc38eb9-9cb2-40ee-80fc-407c7e8c35d7

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_11509 (x : ℝ) (hx: x > 0) : Real.log (x^3 - 2 * x^2 + x + 1) ≥ 0   :=  by sorry

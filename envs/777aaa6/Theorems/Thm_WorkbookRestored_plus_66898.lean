-- Prove2me | Theorems.Thm_WorkbookRestored_plus_66898
-- name    : WorkbookRestored.plus_66898
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:43.852379+00:00
-- url     : https://prove2.me/theorems/b80720c6-f032-4015-a927-38c878a3d2de
-- title:
--   Lean-Workbook Plus 66898: Logarithmic identity
-- statement:
--   $\log_4 6=\log_2\sqrt6$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_66898` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/335e6106-7f09-47c6-b997-340e23777193); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_66898; immutable original Prove2Me node 335e6106-7f09-47c6-b997-340e23777193

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_66898 :
  Real.logb 4 6 = Real.logb 2 (Real.sqrt 6)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_27624
-- name    : WorkbookRestored.plus_27624
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:04.132983+00:00
-- url     : https://prove2.me/theorems/87e37f51-e384-4a0e-b778-7cea2719568c
-- title:
--   Lean-Workbook Plus 27624: Logarithmic identity
-- statement:
--   $(\log_2 3)(\log_3 4)(\log_4 5)(\log_5 6)=\log_2 6$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_27624` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/533ec740-f80c-4d30-938c-7f9fd8382698); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_27624; immutable original Prove2Me node 533ec740-f80c-4d30-938c-7f9fd8382698

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_27624 : (Real.logb 2 3) * (Real.logb 3 4) * (Real.logb 4 5) * (Real.logb 5 6) = Real.logb 2 6   :=  by sorry

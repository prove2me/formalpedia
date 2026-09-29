-- Prove2me | Theorems.Thm_WorkbookRestored_plus_2762
-- name    : WorkbookRestored.plus_2762
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:27:51.550155+00:00
-- url     : https://prove2.me/theorems/0681ba7a-153d-4e71-a04e-97df309ef806
-- title:
--   Lean-Workbook Plus 2762: Logarithmic inequality
-- statement:
--   Show that $x- \ln (1+x)$ is positive for all positive $x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_2762` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/9312d153-9acb-435d-8591-40e40105958b); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_2762; immutable original Prove2Me node 9312d153-9acb-435d-8591-40e40105958b

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_2762 : ∀ x > 0, x - Real.log (1 + x) > 0   :=  by sorry

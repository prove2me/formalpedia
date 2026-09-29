-- Prove2me | Theorems.Thm_WorkbookRestored_plus_9324
-- name    : WorkbookRestored.plus_9324
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:07.226589+00:00
-- url     : https://prove2.me/theorems/5b809696-12ee-4018-843b-4cf2d604e59c
-- title:
--   Lean-Workbook Plus 9324: Trigonometric identity
-- statement:
--   If $\sin a+\cos a=1/5$, then $\sin^3a+\cos^3a=37/125$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_9324` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5c695bb4-8738-47af-8d80-8b805b7477fc); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_9324; immutable original Prove2Me node 5c695bb4-8738-47af-8d80-8b805b7477fc

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_9324 (a : ℝ) (h : sin a + cos a = 1/5) : sin a ^ 3 + cos a ^ 3 = 37/125   :=  by sorry

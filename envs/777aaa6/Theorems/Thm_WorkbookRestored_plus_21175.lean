-- Prove2me | Theorems.Thm_WorkbookRestored_plus_21175
-- name    : WorkbookRestored.plus_21175
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:23.571249+00:00
-- url     : https://prove2.me/theorems/cdd37919-98ed-4d36-abfc-2d5156a5aa0a
-- title:
--   Lean-Workbook Plus 21175: Trigonometric identity
-- statement:
--   Prove the trigonometric identity: \(\sin^2\alpha\cos^2\beta-\cos^2\alpha\sin^2\beta = \sin^2\alpha-\sin^2\beta\)
--
--   Source: Lean-Workbook row `lean_workbook_plus_21175` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/51b9904c-7617-46ee-9033-dc67e35e6a09); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_21175; immutable original Prove2Me node 51b9904c-7617-46ee-9033-dc67e35e6a09

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_21175 (α β : ℝ) : sin α ^ 2 * cos β ^ 2 - cos α ^ 2 * sin β ^ 2 = sin α ^ 2 - sin β ^ 2   :=  by sorry

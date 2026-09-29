-- Prove2me | Theorems.Thm_WorkbookRestored_plus_9318
-- name    : WorkbookRestored.plus_9318
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:07.470171+00:00
-- url     : https://prove2.me/theorems/96f67298-b10a-489a-962d-fefbca3d8383
-- title:
--   Lean-Workbook Plus 9318: Trigonometric identity
-- statement:
--   The special-angle values satisfy $\cos(\pi/2)+\cos(3\pi/2)=0+0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_9318` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6978a4f3-2df4-46e4-8805-6eb1cef9897b); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_9318; immutable original Prove2Me node 6978a4f3-2df4-46e4-8805-6eb1cef9897b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_9318 : Real.cos (π / 2) + Real.cos (3 * π / 2) = 0 + 0   :=  by sorry

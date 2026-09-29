-- Prove2me | Theorems.Thm_WorkbookRestored_plus_32073
-- name    : WorkbookRestored.plus_32073
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:29.912985+00:00
-- url     : https://prove2.me/theorems/df0886dc-b7b7-4440-b40e-26ba4fb3a71c
-- title:
--   Lean-Workbook Plus 32073: Trigonometric identity
-- statement:
--   For every real $x$, $\cos^4x=\tfrac18\cos(4x)+\tfrac12\cos(2x)+\tfrac38$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_32073` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/9d0e25e9-ca42-4c77-932b-e0ca781f6e82); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_32073; immutable original Prove2Me node 9d0e25e9-ca42-4c77-932b-e0ca781f6e82

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_32073 (x : ℝ) : (cos x)^4 = 1 / 8 * cos (4 * x) + 1 / 2 * cos (2 * x) + 3 / 8   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_12106
-- name    : WorkbookRestored.plus_12106
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:18.922549+00:00
-- url     : https://prove2.me/theorems/f9f07fe8-ff4f-4530-88a3-f961019d6ac7
-- title:
--   Lean-Workbook Plus 12106: Trigonometric identity
-- statement:
--   Prove that $\sin(a)\cos(a)+\sin(b)\cos(b)=\sin(a+b)\cos(a-b)$
--
--   Source: Lean-Workbook row `lean_workbook_plus_12106` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/26551301-e44f-499f-b904-3f9c154fce03); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_12106; immutable original Prove2Me node 26551301-e44f-499f-b904-3f9c154fce03

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_12106 (a b : ℝ) : sin a * cos a + sin b * cos b = sin (a + b) * cos (a - b)   :=  by sorry

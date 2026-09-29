-- Prove2me | Theorems.Thm_WorkbookRestored_plus_25157
-- name    : WorkbookRestored.plus_25157
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:30.756996+00:00
-- url     : https://prove2.me/theorems/42e0ada1-419d-42c0-980f-390dd73cd51f
-- title:
--   Lean-Workbook Plus 25157: Trigonometric identity
-- statement:
--   For every real $x$, $\sin x=\cos(\pi/2-x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_25157` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c8788d1a-9d31-49bb-992c-7a2f351a0b4a); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_25157; immutable original Prove2Me node c8788d1a-9d31-49bb-992c-7a2f351a0b4a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_25157 (x : ℝ) : sin x = cos (π / 2 - x)   :=  by sorry

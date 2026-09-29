-- Prove2me | Theorems.Thm_WorkbookRestored_plus_7551
-- name    : WorkbookRestored.plus_7551
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:55.697328+00:00
-- url     : https://prove2.me/theorems/3bb5016e-515b-46da-a383-63f8c442d7ce
-- title:
--   Lean-Workbook Plus 7551: Trigonometric identity
-- statement:
--   Derive the identity \(\sin(x)^4+\cos(x)^4=2\, \left( \cos \left( x \right) \right) ^{4}+1-2\, \left( \cos \left( x \right) \right) ^{2}\).
--
--   Source: Lean-Workbook row `lean_workbook_plus_7551` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/3d9b798b-f803-49c0-8c0e-fca8209d0c0a); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_7551; immutable original Prove2Me node 3d9b798b-f803-49c0-8c0e-fca8209d0c0a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_7551 (x : ℝ) : (sin x)^4 + (cos x)^4 = 2 * (cos x)^4 + 1 - 2 * (cos x)^2   :=  by sorry

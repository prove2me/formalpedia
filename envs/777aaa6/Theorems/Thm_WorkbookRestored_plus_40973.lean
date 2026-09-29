-- Prove2me | Theorems.Thm_WorkbookRestored_plus_40973
-- name    : WorkbookRestored.plus_40973
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:26.167133+00:00
-- url     : https://prove2.me/theorems/16f89a5b-8b8e-4915-81a1-4ef77a61b575
-- title:
--   Lean-Workbook Plus 40973: Trigonometric identity
-- statement:
--   For every real $x$, $x^2-x(\sin x+\cos x)+\sin x\cos x=(x-\sin x)(x-\cos x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_40973` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/155679ae-0397-4c10-8892-e48c29f36be1); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_40973; immutable original Prove2Me node 155679ae-0397-4c10-8892-e48c29f36be1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_40973 (x : ℝ) : x^2 - x * (sin x + cos x) + sin x * cos x = (x - sin x) * (x - cos x)   :=  by sorry

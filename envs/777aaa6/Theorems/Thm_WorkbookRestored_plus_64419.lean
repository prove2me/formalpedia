-- Prove2me | Theorems.Thm_WorkbookRestored_plus_64419
-- name    : WorkbookRestored.plus_64419
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:33.55171+00:00
-- url     : https://prove2.me/theorems/2d2e1778-f425-4f9f-8cd6-bcdf10b4e3c0
-- title:
--   Lean-Workbook Plus 64419: Trigonometric identity
-- statement:
--   $\cos(a+b) \sin(a-b) + \cos (b+c) \sin (b-c) + \cos (c+d) \sin (c-d) + \cos (d+a) \sin (d-a) =0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_64419` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/21a31ed0-ec16-4f04-a653-a7ff7a6a29a2); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_64419; immutable original Prove2Me node 21a31ed0-ec16-4f04-a653-a7ff7a6a29a2

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_64419 (a b c d : ℝ) : cos (a + b) * sin (a - b) + cos (b + c) * sin (b - c) + cos (c + d) * sin (c - d) + cos (d + a) * sin (d - a) = 0   :=  by sorry

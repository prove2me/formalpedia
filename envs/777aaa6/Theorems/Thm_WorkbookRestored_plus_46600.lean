-- Prove2me | Theorems.Thm_WorkbookRestored_plus_46600
-- name    : WorkbookRestored.plus_46600
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:20.797114+00:00
-- url     : https://prove2.me/theorems/d33ed362-51c8-423b-9416-714d7d490003
-- title:
--   Lean-Workbook Plus 46600: Trigonometric identity
-- statement:
--   For real $x,y,n$, $\cos(x-y)-\cos(x+y)=n$ if and only if $2\cos^2((x-y)/2)-2\cos^2((x+y)/2)=n$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_46600` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/8da09457-cde9-4f70-8315-f0bb70f5c4aa); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_46600; immutable original Prove2Me node 8da09457-cde9-4f70-8315-f0bb70f5c4aa

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_46600 (x y n : ℝ) : (cos (x - y) - cos (x + y) = n ↔ 2 * cos ((x - y) / 2) ^ 2 - 2 * cos ((x + y) / 2) ^ 2 = n)   :=  by sorry

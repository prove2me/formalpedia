-- Prove2me | Theorems.Thm_WorkbookRestored_plus_49730
-- name    : WorkbookRestored.plus_49730
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:55.298713+00:00
-- url     : https://prove2.me/theorems/bcbb662f-211f-4d52-a242-e031c418c02d
-- title:
--   Lean-Workbook Plus 49730: Trigonometric identity
-- statement:
--   For real $x,y,z$, $\sin(x-y)\sin(z-x)=\tfrac12(\cos(2x-y-z)-\cos(z-y))$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_49730` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/ad9a8cee-97b6-446c-bf20-982843666933); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_49730; immutable original Prove2Me node ad9a8cee-97b6-446c-bf20-982843666933

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_49730 (x y z : ℝ) : Real.sin (x - y) * Real.sin (z - x) = 1/2 * (Real.cos (2 * x - y - z) - Real.cos (z - y))   :=  by sorry

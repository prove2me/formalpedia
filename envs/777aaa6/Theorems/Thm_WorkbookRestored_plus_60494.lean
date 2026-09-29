-- Prove2me | Theorems.Thm_WorkbookRestored_plus_60494
-- name    : WorkbookRestored.plus_60494
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:26.092049+00:00
-- url     : https://prove2.me/theorems/95c6362f-5929-47d3-8094-ded5ff0c177d
-- title:
--   Lean-Workbook Plus 60494: Logarithmic inequality
-- statement:
--   $\log \left ( \tan \left ( \frac{\pi}{4}-a \right ) \right ) =-\log \left ( \tan \left ( \frac{\pi}{4}+a \right ) \right )$ for $0<a<\frac{\pi}{4}$
--
--   Source: Lean-Workbook row `lean_workbook_plus_60494` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/95bb9098-dfbd-4098-a2ca-88ff8fcb04f7); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_60494; immutable original Prove2Me node 95bb9098-dfbd-4098-a2ca-88ff8fcb04f7

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_60494 (a : ℝ) (ha : 0 < a ∧ a < Real.pi / 4) : Real.log (Real.tan (Real.pi / 4 - a)) = -Real.log (Real.tan (Real.pi / 4 + a))   :=  by sorry

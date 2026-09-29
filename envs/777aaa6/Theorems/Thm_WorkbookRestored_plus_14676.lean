-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14676
-- name    : WorkbookRestored.plus_14676
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:32.966186+00:00
-- url     : https://prove2.me/theorems/8ecbad33-b78e-4813-aca3-9095b4d8871e
-- title:
--   Lean-Workbook Plus 14676: Trigonometric identity
-- statement:
--   Prove that $sin(x+y)sin(y+z)=sin(y)sin(x+y+z)+sin(z)sin(x)$ .
--
--   Source: Lean-Workbook row `lean_workbook_plus_14676` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4660f15f-1181-4f8c-a23b-4429a8d0be24); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14676; immutable original Prove2Me node 4660f15f-1181-4f8c-a23b-4429a8d0be24

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_14676 : ∀ x y z : ℝ, sin (x + y) * sin (y + z) = sin y * sin (x + y + z) + sin z * sin x   :=  by sorry

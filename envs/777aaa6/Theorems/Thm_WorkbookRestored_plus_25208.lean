-- Prove2me | Theorems.Thm_WorkbookRestored_plus_25208
-- name    : WorkbookRestored.plus_25208
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:35.09648+00:00
-- url     : https://prove2.me/theorems/dc723fdd-3162-4557-98ba-ace34078dd63
-- title:
--   Lean-Workbook Plus 25208: Trigonometric identity
-- statement:
--   For every natural number $n$, $2\cos(\pi/2^{n+1})+2=4\cos^2(\pi/2^{n+2})$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_25208` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/0cbc34ae-924a-40dc-b992-e930a947a072); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_25208; immutable original Prove2Me node 0cbc34ae-924a-40dc-b992-e930a947a072

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_25208 : ∀ n : ℕ, 2 * Real.cos (π / 2 ^ (n + 1)) + 2 = 4 * (Real.cos (π / 2 ^ (n + 2))) ^ 2   :=  by sorry

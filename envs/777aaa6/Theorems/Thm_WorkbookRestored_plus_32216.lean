-- Prove2me | Theorems.Thm_WorkbookRestored_plus_32216
-- name    : WorkbookRestored.plus_32216
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:31.582299+00:00
-- url     : https://prove2.me/theorems/0681f913-6919-41da-af3d-5355a01057b8
-- title:
--   Lean-Workbook Plus 32216: Trigonometric identity
-- statement:
--   For real $a,b,c$, $\cos(a+b+c)+\cos(a+b-c)+\cos(a+c-b)+\cos(b+c-a)=4\cos a\cos b\cos c$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_32216` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/07bc0f71-f2ec-4ba2-8e89-cb6bcac9ba77); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_32216; immutable original Prove2Me node 07bc0f71-f2ec-4ba2-8e89-cb6bcac9ba77

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_32216 {a b c : ℝ} : (Real.cos (a + b + c) + Real.cos (a + b - c) + Real.cos (a + c - b) + Real.cos (b + c - a)) = 4 * Real.cos a * Real.cos b * Real.cos c   :=  by sorry

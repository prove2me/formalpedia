-- Prove2me | Theorems.Thm_WorkbookRestored_plus_19270
-- name    : WorkbookRestored.plus_19270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:07.81351+00:00
-- url     : https://prove2.me/theorems/f37ce963-bbdc-4012-ada8-0c1df1b3c1ef
-- title:
--   Lean-Workbook Plus 19270: Trigonometric identity
-- statement:
--   If $\sin x\ne0$ and $\cos x\ne0$, then $\tan x+1/\tan x=1/(\sin x\cos x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_19270` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/cb9c721a-ae5b-405c-ad8b-ecb20a83a0f2); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_19270; immutable original Prove2Me node cb9c721a-ae5b-405c-ad8b-ecb20a83a0f2

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_19270 (x : ℝ) (hx : sin x ≠ 0 ∧ cos x ≠ 0) : tan x + 1 / tan x = 1 / (sin x * cos x)   :=  by sorry

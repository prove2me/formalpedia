-- Prove2me | Theorems.Thm_WorkbookRestored_plus_19576
-- name    : WorkbookRestored.plus_19576
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:12.429641+00:00
-- url     : https://prove2.me/theorems/9e54d72b-ffd3-41fd-8afa-a296a832cb48
-- title:
--   Lean-Workbook Plus 19576: Trigonometric inequality
-- statement:
--   If $\tan x<0$, then $\sin x$ and $\cos x$ are both nonzero and $\sin x\cos x<0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_19576` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/13dfb87a-5664-4692-83fb-506aa6c89f0e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_19576; immutable original Prove2Me node 13dfb87a-5664-4692-83fb-506aa6c89f0e

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_19576 (x : ℝ) (hx : tan x < 0) : (sin x ≠ 0 ∧ cos x ≠ 0 ∧ sin x * cos x < 0)   :=  by sorry

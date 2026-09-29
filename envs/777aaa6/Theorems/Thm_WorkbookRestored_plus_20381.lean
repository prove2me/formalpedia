-- Prove2me | Theorems.Thm_WorkbookRestored_plus_20381
-- name    : WorkbookRestored.plus_20381
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:19.298044+00:00
-- url     : https://prove2.me/theorems/505e597b-ee7f-4317-8587-240776463547
-- title:
--   Lean-Workbook Plus 20381: Trigonometric identity
-- statement:
--   The special-angle tangent value is $\tan(\pi/2+\pi/4)=-1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_20381` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/7b74378e-1a91-493a-bd2a-96b4ada48ca6); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_20381; immutable original Prove2Me node 7b74378e-1a91-493a-bd2a-96b4ada48ca6

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_20381 (x : ℝ) : tan (π / 2 + π / 4) = -1   :=  by sorry

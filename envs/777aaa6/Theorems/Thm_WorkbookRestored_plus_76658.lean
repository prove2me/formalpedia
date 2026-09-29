-- Prove2me | Theorems.Thm_WorkbookRestored_plus_76658
-- name    : WorkbookRestored.plus_76658
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:18:00.006075+00:00
-- url     : https://prove2.me/theorems/17a47af4-dc11-4a44-b965-b9b43c4b8be4
-- title:
--   Lean-Workbook Plus 76658: Exponential inequality
-- statement:
--   $(1-u)^{1/u}<e^{-1}$ for $0<u<1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_76658` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/1136b1a7-cb68-484c-b34d-95ccff141502); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_76658; immutable original Prove2Me node 1136b1a7-cb68-484c-b34d-95ccff141502

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_76658 : ∀ u : ℝ, 0 < u ∧ u < 1 → (1 - u) ^ (1 / u) < exp (-1)   :=  by sorry

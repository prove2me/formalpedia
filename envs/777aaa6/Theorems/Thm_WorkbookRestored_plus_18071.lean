-- Prove2me | Theorems.Thm_WorkbookRestored_plus_18071
-- name    : WorkbookRestored.plus_18071
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:03.195998+00:00
-- url     : https://prove2.me/theorems/1284bacf-46a7-44b3-905c-86cdf57e5c26
-- title:
--   Lean-Workbook Plus 18071: Trigonometric inequality
-- statement:
--   Prove that $ \tan x$ is increasing on $ \Big]-\frac\pi2,\frac\pi2\Big[$
--
--   Source: Lean-Workbook row `lean_workbook_plus_18071` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/03dbffc1-2456-4903-a432-67b6b335951d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_18071; immutable original Prove2Me node 03dbffc1-2456-4903-a432-67b6b335951d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_18071 : ∀ x y : ℝ, x ∈ Set.Ioo (-π / 2) (π / 2) ∧ y ∈ Set.Ioo (-π / 2) (π / 2) ∧ x < y → tan x < tan y   :=  by sorry

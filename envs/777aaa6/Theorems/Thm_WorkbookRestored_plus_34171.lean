-- Prove2me | Theorems.Thm_WorkbookRestored_plus_34171
-- name    : WorkbookRestored.plus_34171
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:56.20144+00:00
-- url     : https://prove2.me/theorems/3c83f265-50c7-48ed-b0b6-27df8beacac9
-- title:
--   Lean-Workbook Plus 34171: Trigonometric inequality
-- statement:
--   For every real $C$, $\sin C(1-\sin C)\le1/4$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34171` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/7f152dbb-4b80-4f53-a649-4bdbe9861869); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34171; immutable original Prove2Me node 7f152dbb-4b80-4f53-a649-4bdbe9861869

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_34171 : ∀ C : ℝ, sin C * (1 - sin C) ≤ 1 / 4   :=  by sorry

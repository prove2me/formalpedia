-- Prove2me | Theorems.Thm_WorkbookRestored_plus_12542
-- name    : WorkbookRestored.plus_12542
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:25.173229+00:00
-- url     : https://prove2.me/theorems/09767d4d-fe11-4359-bc2a-094b0932ba6b
-- title:
--   Lean-Workbook Plus 12542: Trigonometric inequality
-- statement:
--   For all real $r_1,r_2,\theta$, $(1-\cos\theta)(r_1-r_2)^2\ge0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_12542` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/b017fc35-9fc8-4bff-ba6d-bdad1e5bb6d8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_12542; immutable original Prove2Me node b017fc35-9fc8-4bff-ba6d-bdad1e5bb6d8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_12542 (r₁ r₂ : ℝ) (θ : ℝ) : (1 - Real.cos θ) * (r₁ - r₂) ^ 2 ≥ 0   :=  by sorry

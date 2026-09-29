-- Prove2me | Theorems.Thm_WorkbookRestored_plus_34146
-- name    : WorkbookRestored.plus_34146
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:50.043416+00:00
-- url     : https://prove2.me/theorems/93e74436-eb4c-495c-9357-07cc59ad42cc
-- title:
--   Lean-Workbook Plus 34146: Logarithmic inequality
-- statement:
--   If $1<x<y$, then $(x-1)\log x<(y-1)\log y$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34146` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6556d155-1988-48cc-8032-b46deb58d964); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34146; immutable original Prove2Me node 6556d155-1988-48cc-8032-b46deb58d964

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_34146 (x y : ℝ) (h₁ : 1 < x) (h₂ : 1 < y) (h₃ : x < y) : (x - 1) * Real.log x < (y - 1) * Real.log y   :=  by sorry

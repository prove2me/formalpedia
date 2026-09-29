-- Prove2me | Theorems.Thm_WorkbookRestored_plus_31096
-- name    : WorkbookRestored.plus_31096
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:23.052985+00:00
-- url     : https://prove2.me/theorems/46fc90f4-64e6-4d74-80ce-1c77be51440b
-- title:
--   Lean-Workbook Plus 31096: Trigonometric inequality
-- statement:
--   For real $A,B,C$, $\cos(A-B)+\cos(B-C)+\cos(C-A)\le3$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_31096` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/d4983142-85aa-471b-84a4-f619e2beff88); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_31096; immutable original Prove2Me node d4983142-85aa-471b-84a4-f619e2beff88

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_31096 (A B C : ℝ) : Real.cos (A - B) + Real.cos (B - C) + Real.cos (C - A) ≤ 3   :=  by sorry

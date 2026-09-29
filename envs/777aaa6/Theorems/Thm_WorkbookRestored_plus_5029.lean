-- Prove2me | Theorems.Thm_WorkbookRestored_plus_5029
-- name    : WorkbookRestored.plus_5029
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:36.755981+00:00
-- url     : https://prove2.me/theorems/c6a5b821-a0c2-44f4-8a8b-110ef02f6ca3
-- title:
--   Lean-Workbook Plus 5029: Trigonometric identity
-- statement:
--   Prove that $3 \sin a - 4 \sin^{3}a = \sin 3a$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_5029` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/255d26ea-bcd0-4d81-bf38-e7d0d2a5042b); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_5029; immutable original Prove2Me node 255d26ea-bcd0-4d81-bf38-e7d0d2a5042b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_5029 (a : ℝ) : 3 * Real.sin a - 4 * (Real.sin a)^3 = Real.sin (3 * a)   :=  by sorry

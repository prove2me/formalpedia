-- Prove2me | Theorems.Thm_WorkbookRestored_plus_74920
-- name    : WorkbookRestored.plus_74920
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:58.84592+00:00
-- url     : https://prove2.me/theorems/aebcf66a-e1c6-4ef8-9177-c0bd9595629c
-- title:
--   Lean-Workbook Plus 74920: Exponential inequality
-- statement:
--   for x > 1, \(x^{2}e^{-x^{9}}<x^{2}e^{-x^{3}}\).
--
--   Source: Lean-Workbook row `lean_workbook_plus_74920` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/aec7c362-157b-4de5-8427-16a0c123ca90); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_74920; immutable original Prove2Me node aec7c362-157b-4de5-8427-16a0c123ca90

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_74920 (x : ℝ) (hx : 1 < x) : x^2 * (Real.exp (-x^9)) < x^2 * (Real.exp (-x^3))   :=  by sorry

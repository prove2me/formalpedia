-- Prove2me | Theorems.Thm_WorkbookRestored_plus_80943
-- name    : WorkbookRestored.plus_80943
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:21:09.460816+00:00
-- url     : https://prove2.me/theorems/8a9c4c0d-eb88-4b9a-adc0-99bf6d3643c0
-- title:
--   Lean-Workbook Plus 80943: Trigonometric identity
-- statement:
--   $\sin(a+b-2c) \cos b - \sin (a+c-2b) \cos c$
--
--    $= \sin (b-c) \{ \cos (b+c-a) + \cos (a+c-b) + \cos (a+b-c) \}$ .
--
--   Source: Lean-Workbook row `lean_workbook_plus_80943` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/f94d3ef6-97b4-44c4-aa12-078058a9502e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_80943; immutable original Prove2Me node f94d3ef6-97b4-44c4-aa12-078058a9502e

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_80943 (a b c : ℝ) :
  Real.sin (a + b - 2 * c) * Real.cos b - Real.sin (a + c - 2 * b) * Real.cos c
  = Real.sin (b - c) * (Real.cos (b + c - a) + Real.cos (a + c - b) + Real.cos (a + b - c))   :=  by sorry

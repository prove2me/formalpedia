-- Prove2me | Theorems.Thm_WorkbookRestored_plus_19379
-- name    : WorkbookRestored.plus_19379
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:11.509657+00:00
-- url     : https://prove2.me/theorems/836c6e3d-8747-4bcd-9256-e3c0e4381c2c
-- title:
--   Lean-Workbook Plus 19379: Trigonometric inequality
-- statement:
--   For every $x\in[0,\pi/2]$, $1\le2-\sin x+\cos x\le3$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_19379` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/29cf79bc-c978-4461-b1df-79ba1b418e31); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_19379; immutable original Prove2Me node 29cf79bc-c978-4461-b1df-79ba1b418e31

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_19379 (x: ℝ) (hx: 0 ≤ x ∧ x ≤ π/2) :
  1 ≤ 2 - Real.sin x + Real.cos x ∧ 2 - Real.sin x + Real.cos x ≤ 3   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_28301
-- name    : WorkbookRestored.plus_28301
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:16.804263+00:00
-- url     : https://prove2.me/theorems/c89330fc-93c1-4b6c-960f-bb1293505301
-- title:
--   Lean-Workbook Plus 28301: Trigonometric identity
-- statement:
--   For every real $\theta$, $\cos\theta+\cos(\theta+2\pi/3)+\cos(\theta+4\pi/3)=0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_28301` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/b41a2f33-6bd1-4b9d-8c81-e4ce41d6f657); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_28301; immutable original Prove2Me node b41a2f33-6bd1-4b9d-8c81-e4ce41d6f657

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_28301 (θ : ℝ) : Real.cos θ + Real.cos (θ + (2 * Real.pi / 3)) + Real.cos (θ + (4 * Real.pi / 3)) = 0   :=  by sorry

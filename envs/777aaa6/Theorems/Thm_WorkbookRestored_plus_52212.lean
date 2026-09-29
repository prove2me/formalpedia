-- Prove2me | Theorems.Thm_WorkbookRestored_plus_52212
-- name    : WorkbookRestored.plus_52212
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:16:39.432051+00:00
-- url     : https://prove2.me/theorems/cc9563a2-367b-464b-a2e8-cbd37ef03766
-- title:
--   Lean-Workbook Plus 52212: Trigonometric inequality
-- statement:
--   For $\pi < \theta < \frac{3\pi}{2}$ , $sin(\theta) < 0$ and $cos(\theta) < 0$ .
--
--   Source: Lean-Workbook row `lean_workbook_plus_52212` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/72554e9d-2ac6-44d2-83a1-60c1045a0506); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_52212; immutable original Prove2Me node 72554e9d-2ac6-44d2-83a1-60c1045a0506

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_52212 (θ : ℝ) (h₁ : π < θ) (h₂ : θ < 3 * π / 2) : sin θ < 0 ∧ cos θ < 0   :=  by sorry

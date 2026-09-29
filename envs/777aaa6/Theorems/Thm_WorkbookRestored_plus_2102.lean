-- Prove2me | Theorems.Thm_WorkbookRestored_plus_2102
-- name    : WorkbookRestored.plus_2102
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:27:47.66262+00:00
-- url     : https://prove2.me/theorems/22632121-d511-45de-a8e5-26ad79bea189
-- title:
--   Lean-Workbook Plus 2102: Trigonometric identity
-- statement:
--   For every real angle $\theta$, the double-angle identity is $\sin(2\theta)=2\tan\theta/(1+\tan^2\theta)$, with the usual total real operations used by Lean.
--
--   Source: Lean-Workbook row `lean_workbook_plus_2102` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5f2ae95c-754d-4362-8926-50bb6daff46c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_2102; immutable original Prove2Me node 5f2ae95c-754d-4362-8926-50bb6daff46c

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_2102 (θ : ℝ) : sin (2 * θ) = 2 * tan θ / (1 + tan θ ^ 2)   :=  by sorry

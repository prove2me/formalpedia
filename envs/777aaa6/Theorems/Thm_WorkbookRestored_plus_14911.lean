-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14911
-- name    : WorkbookRestored.plus_14911
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:38.730571+00:00
-- url     : https://prove2.me/theorems/9ddcd3eb-b3a2-455d-bb6b-e44204cf3c7c
-- title:
--   Lean-Workbook Plus 14911: Trigonometric inequality
-- statement:
--   On $[0,\pi/2]$, sine is strictly increasing and cosine is strictly decreasing: if $x<y$ in this interval, then $\sin x<\sin y$ and $\cos y<\cos x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_14911` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/e2b6098f-7a0b-4ac9-8905-65f1790e3615); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14911; immutable original Prove2Me node e2b6098f-7a0b-4ac9-8905-65f1790e3615

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_14911 : ∀ x y : ℝ, x ∈ Set.Icc 0 (π / 2) ∧ y ∈ Set.Icc 0 (π / 2) → x < y → sin x < sin y ∧ cos y < cos x   :=  by sorry

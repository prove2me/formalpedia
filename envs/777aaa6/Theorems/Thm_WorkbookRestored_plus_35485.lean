-- Prove2me | Theorems.Thm_WorkbookRestored_plus_35485
-- name    : WorkbookRestored.plus_35485
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:07.52149+00:00
-- url     : https://prove2.me/theorems/395fdd37-ed2e-47e1-9f58-97817ea47490
-- title:
--   Lean-Workbook Plus 35485: Trigonometric inequality
-- statement:
--   If $y=2\sin p$ and $-\pi/2\le p\le\pi/2$, then $-2\le y\le2$. This gives the bounding component of the source’s range question.
--
--   Source: Lean-Workbook row `lean_workbook_plus_35485` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a50710b9-1837-47a4-b1dc-e5df4dfa51d8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_35485; immutable original Prove2Me node a50710b9-1837-47a4-b1dc-e5df4dfa51d8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_35485 (p y : ℝ) (h₁ : y = 2 * Real.sin p) (h₂ : -Real.pi / 2 ≤ p ∧ p ≤ Real.pi / 2) : -2 ≤ y ∧ y ≤ 2   :=  by sorry

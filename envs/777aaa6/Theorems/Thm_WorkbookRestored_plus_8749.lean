-- Prove2me | Theorems.Thm_WorkbookRestored_plus_8749
-- name    : WorkbookRestored.plus_8749
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:02.589088+00:00
-- url     : https://prove2.me/theorems/861fbb37-0dfe-4331-89c9-d5c7884d3844
-- title:
--   Lean-Workbook Plus 8749: Trigonometric inequality
-- statement:
--   If $0<x\le\pi/2$, then $0<\sin x\le1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_8749` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/e83167e5-49b8-4166-b10a-16fae07390d6); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_8749; immutable original Prove2Me node e83167e5-49b8-4166-b10a-16fae07390d6

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_8749 : ∀ x : ℝ, 0 < x ∧ x ≤ π / 2 → 0 < sin x ∧ sin x ≤ 1   :=  by sorry

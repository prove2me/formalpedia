-- Prove2me | Theorems.Thm_WorkbookRestored_plus_23560
-- name    : WorkbookRestored.plus_23560
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:19.77512+00:00
-- url     : https://prove2.me/theorems/33646319-d149-4e4e-a02e-b799a7c3792d
-- title:
--   Lean-Workbook Plus 23560: Trigonometric inequality
-- statement:
--   For real $a,A$, $a^2-2a\cos A+\cos^2 A-3\sin^2 A\le0$ if and only if $(a-\cos A+\sqrt3\sin A)(a-\cos A-\sqrt3\sin A)\le0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_23560` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/796305d9-2b19-4946-9c3e-440fe5b278ad); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_23560; immutable original Prove2Me node 796305d9-2b19-4946-9c3e-440fe5b278ad

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_23560 (a : ℝ) (A : ℝ) : a^2 + (-2 * Real.cos A) * a + (Real.cos A)^2 - 3 * (Real.sin A)^2 ≤ 0 ↔ (a - Real.cos A + Real.sqrt 3 * Real.sin A) * (a - Real.cos A - Real.sqrt 3 * Real.sin A) ≤ 0   :=  by sorry

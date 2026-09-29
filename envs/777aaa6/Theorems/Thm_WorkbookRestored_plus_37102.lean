-- Prove2me | Theorems.Thm_WorkbookRestored_plus_37102
-- name    : WorkbookRestored.plus_37102
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:16.606537+00:00
-- url     : https://prove2.me/theorems/ed1e1085-7b01-423e-9fa2-ccec0edb7bd0
-- title:
--   Lean-Workbook Plus 37102: Trigonometric identity
-- statement:
--   For real $a,b,c,A$, $\frac{b\sin A(a^2+c^2-b^2-b^2-c^2+a^2)}{2abc}=\frac{b\sin A(2a^2-2b^2)}{2abc}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_37102` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/fde68700-a4c0-42b1-9732-3be60d00da02); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_37102; immutable original Prove2Me node fde68700-a4c0-42b1-9732-3be60d00da02

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_37102 (a b c A : ℝ) : (b * Real.sin A * (a^2 + c^2 - b^2 - b^2 - c^2 + a^2)) / (2 * a * b * c) = (b * Real.sin A * (2 * a^2 - 2 * b^2)) / (2 * a * b * c)   :=  by sorry

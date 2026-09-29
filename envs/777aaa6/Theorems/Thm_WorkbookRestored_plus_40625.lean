-- Prove2me | Theorems.Thm_WorkbookRestored_plus_40625
-- name    : WorkbookRestored.plus_40625
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:24.129981+00:00
-- url     : https://prove2.me/theorems/516e1095-be57-4a7c-b079-17a2a5d9c42d
-- title:
--   Lean-Workbook Plus 40625: Trigonometric identity
-- statement:
--   If $a=\cos\alpha$ and $b=\sin\alpha/\sqrt3$, then $a^2+3b^2=1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_40625` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/53af00af-a3c1-4686-a89c-286871ec46a4); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_40625; immutable original Prove2Me node 53af00af-a3c1-4686-a89c-286871ec46a4

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_40625 (a b : ℝ) (α : ℝ) (h₁ : a = Real.cos α) (h₂ : b = Real.sin α / Real.sqrt 3) : a^2 + 3 * b^2 = 1   :=  by sorry

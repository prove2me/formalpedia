-- Prove2me | Theorems.Thm_WorkbookRestored_plus_31376
-- name    : WorkbookRestored.plus_31376
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:24.928796+00:00
-- url     : https://prove2.me/theorems/843b3899-d84f-4e1c-9e74-81672c01c399
-- title:
--   Lean-Workbook Plus 31376: Trigonometric identity
-- statement:
--   For all real $x,y$, $\cos(\arcsin x)-\sqrt{1-x^2}=\cos(\arcsin y)-\sqrt{1-y^2}$. Lean’s total real inverse sine and square root are used, including outside $[-1,1]$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_31376` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/268a6dd7-ac3b-4ee9-8c9c-fd76b0043167); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_31376; immutable original Prove2Me node 268a6dd7-ac3b-4ee9-8c9c-fd76b0043167

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
open Real

theorem WorkbookRestored.plus_31376 x y : cos (arcsin x) - Real.sqrt (1 - x ^ 2) = cos (arcsin y) - Real.sqrt (1 - y ^ 2)   :=  by sorry

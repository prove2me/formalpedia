-- Prove2me | Theorems.Thm_WorkbookRestored_plus_73087
-- name    : WorkbookRestored.plus_73087
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:56.040046+00:00
-- url     : https://prove2.me/theorems/78cb2313-afbc-4991-9107-2b85a62081df
-- title:
--   Lean-Workbook Plus 73087: Trigonometric identity
-- statement:
--   For real $A,B$, $\sin A\cos B=\sin B\cos A$ if and only if $\sin(A-B)=0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_73087` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/67704f6f-4805-4024-8c4b-8daac72dc664); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_73087; immutable original Prove2Me node 67704f6f-4805-4024-8c4b-8daac72dc664

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_73087 :
  ∀ A B : ℝ, (sin A * cos B = sin B * cos A) ↔ sin (A - B) = 0   :=  by sorry

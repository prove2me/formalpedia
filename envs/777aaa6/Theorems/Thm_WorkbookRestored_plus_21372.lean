-- Prove2me | Theorems.Thm_WorkbookRestored_plus_21372
-- name    : WorkbookRestored.plus_21372
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:21.798817+00:00
-- url     : https://prove2.me/theorems/aef8a9b9-5bd1-445d-b3b3-7dd3a1a47bce
-- title:
--   Lean-Workbook Plus 21372: Trigonometric identity
-- statement:
--   Prove the identity: $\cos{x}+\cos{y}=2\cos{\frac{x+y}{2}}\cos{\frac{x-y}{2}}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_21372` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/359a9297-1102-4bf0-abcc-79501314c20c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_21372; immutable original Prove2Me node 359a9297-1102-4bf0-abcc-79501314c20c

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_21372 : ∀ x y : ℝ, cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2)   :=  by sorry

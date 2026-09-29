-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14729
-- name    : WorkbookRestored.plus_14729
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:31.757214+00:00
-- url     : https://prove2.me/theorems/3c59ddc7-4e63-48fb-a385-44700bbf2458
-- title:
--   Lean-Workbook Plus 14729: Trigonometric inequality
-- statement:
--   For every real angle $A$, $\tfrac94-4(\sin(A/2)-\tfrac14)^2\le\tfrac94$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_14729` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/178b872c-a50b-4048-b7cb-c3e6c4061967); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14729; immutable original Prove2Me node 178b872c-a50b-4048-b7cb-c3e6c4061967

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_14729 : ∀ A : ℝ, (9 / 4 - 4 * (Real.sin (A / 2) - 1 / 4) ^ 2) ≤ 9 / 4   :=  by sorry

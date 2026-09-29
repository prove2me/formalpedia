-- Prove2me | Theorems.Thm_WorkbookRestored_plus_26146
-- name    : WorkbookRestored.plus_26146
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:43.640957+00:00
-- url     : https://prove2.me/theorems/dbbe87c8-2eca-4902-af8f-d7ea10a6fbb0
-- title:
--   Lean-Workbook Plus 26146: Trigonometric inequality
-- statement:
--   For every real $x$, $|\cos x\sin x|\le1/2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_26146` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/22f18fbb-44f8-490a-941d-8854140aca9b); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_26146; immutable original Prove2Me node 22f18fbb-44f8-490a-941d-8854140aca9b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_26146 : ∀ x : ℝ, |cos x * sin x| ≤ 1 / 2   :=  by sorry

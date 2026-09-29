-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14089
-- name    : WorkbookRestored.plus_14089
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:33.930287+00:00
-- url     : https://prove2.me/theorems/ebc66b79-fe34-4f7b-ae03-c560fd0e65a7
-- title:
--   Lean-Workbook Plus 14089: Trigonometric inequality
-- statement:
--   Prove that $2\sin(\alpha)^2+2\sin(\beta)^2+2 \geq 2\sin(\alpha)+2\sin(\beta)+2\sin(\alpha)\sin(\beta)$
--
--   Source: Lean-Workbook row `lean_workbook_plus_14089` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a8c28f94-dcc6-4f3c-8208-2146be26388d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14089; immutable original Prove2Me node a8c28f94-dcc6-4f3c-8208-2146be26388d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_14089 (α β : ℝ) : 2 * sin α ^ 2 + 2 * sin β ^ 2 + 2 ≥ 2 * sin α + 2 * sin β + 2 * sin α * sin β   :=  by sorry

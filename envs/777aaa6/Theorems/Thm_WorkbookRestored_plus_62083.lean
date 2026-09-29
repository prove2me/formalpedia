-- Prove2me | Theorems.Thm_WorkbookRestored_plus_62083
-- name    : WorkbookRestored.plus_62083
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:29.04289+00:00
-- url     : https://prove2.me/theorems/315f9dea-9229-42a5-b96a-f566e184ab6c
-- title:
--   Lean-Workbook Plus 62083: Trigonometric identity
-- statement:
--   For real $\alpha,\beta$ with $\alpha+\beta=\pi/4$, $\cos\alpha\sin\alpha+\sin^2\beta=\cos\beta\sin\beta+\sin^2\alpha$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_62083` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a85dfdf4-c5e8-4dc5-808a-c499f927e9e0); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_62083; immutable original Prove2Me node a85dfdf4-c5e8-4dc5-808a-c499f927e9e0

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_62083 (α β : ℝ) (h₁ : α + β = π / 4) : cos α * sin α + sin β ^ 2 = cos β * sin β + sin α ^ 2   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_80657
-- name    : WorkbookRestored.plus_80657
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:21:09.158229+00:00
-- url     : https://prove2.me/theorems/430f60ef-866b-455c-9574-832237ec88c5
-- title:
--   Lean-Workbook Plus 80657: Trigonometric identity
-- statement:
--   For real $\alpha,\theta$ with $\cos(2\alpha)=7/25$ and $\sin(2\alpha)=24/25$, $\cos(2\alpha+2\theta)=(7\cos(2\theta)-24\sin(2\theta))/25$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_80657` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/b4413f25-e5fe-4f51-bf7f-a0400d7d150c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_80657; immutable original Prove2Me node b4413f25-e5fe-4f51-bf7f-a0400d7d150c

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_80657 (α θ : ℝ) (h₁ : cos (2 * α) = 7 / 25) (h₂ : sin (2 * α) = 24 / 25) : cos (2 * α + 2 * θ) = (7 * cos (2 * θ) - 24 * sin (2 * θ)) / 25   :=  by sorry

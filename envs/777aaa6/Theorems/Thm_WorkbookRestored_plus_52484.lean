-- Prove2me | Theorems.Thm_WorkbookRestored_plus_52484
-- name    : WorkbookRestored.plus_52484
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:16:59.48598+00:00
-- url     : https://prove2.me/theorems/00ea120a-cc30-4084-a9e0-4670390a4e21
-- title:
--   Lean-Workbook Plus 52484: Trigonometric inequality
-- statement:
--   For $-\pi/2\le x\le\pi/2$, $\sin^2x+\cos x-5/4\le0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_52484` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/8e639972-9d15-4e03-9494-d1a1b879e14d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_52484; immutable original Prove2Me node 8e639972-9d15-4e03-9494-d1a1b879e14d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_52484 :
  ∀ x ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2), (Real.sin x)^2 + Real.cos x - 5 / 4 ≤ 0   :=  by sorry

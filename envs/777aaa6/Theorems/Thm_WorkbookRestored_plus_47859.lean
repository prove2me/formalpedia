-- Prove2me | Theorems.Thm_WorkbookRestored_plus_47859
-- name    : WorkbookRestored.plus_47859
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:51.68695+00:00
-- url     : https://prove2.me/theorems/1a8911ce-14c2-4215-bd7e-fdc1b7872a85
-- title:
--   Lean-Workbook Plus 47859: Trigonometric inequality
-- statement:
--   For $0<\theta<\pi/2$, $\tan\theta(1-\sin\theta)<2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_47859` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c1ccb860-9d4c-47e9-b36d-e72b287c5207); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_47859; immutable original Prove2Me node c1ccb860-9d4c-47e9-b36d-e72b287c5207

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_47859 (θ : ℝ) (h1 : 0 < θ) (h2 : θ < Real.pi / 2) : 2 > Real.tan θ * (1 - Real.sin θ)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_78015
-- name    : WorkbookRestored.plus_78015
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:18:04.883449+00:00
-- url     : https://prove2.me/theorems/d7d0765e-c6e1-4ce1-9ac3-1c2b4e6152cc
-- title:
--   Lean-Workbook Plus 78015: Trigonometric inequality
-- statement:
--   If $0\le\alpha\le\pi/2$ and $\cos\alpha=60/61$, then $\sin(\alpha/2)=\sqrt{122}/122$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_78015` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/07451695-0fbf-41d2-93ce-404653489d2f); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_78015; immutable original Prove2Me node 07451695-0fbf-41d2-93ce-404653489d2f

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_78015 (α : ℝ) (h₁ : 0 ≤ α) (h₂ : α ≤ π/2) (h₃ : cos α = 60/61) : sin (α/2) = √122 / 122   :=  by sorry

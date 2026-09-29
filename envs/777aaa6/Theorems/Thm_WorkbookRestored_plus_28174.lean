-- Prove2me | Theorems.Thm_WorkbookRestored_plus_28174
-- name    : WorkbookRestored.plus_28174
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:12.733251+00:00
-- url     : https://prove2.me/theorems/4bcb0678-8fc5-4904-bd35-9d95ce837584
-- title:
--   Lean-Workbook Plus 28174: Trigonometric identity
-- statement:
--   If $\alpha=\pi-(\beta+\gamma)$, then $\cos\alpha=-\cos(\gamma+\beta)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_28174` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/dd016d64-f144-4085-a2f2-e67d7b3c3838); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_28174; immutable original Prove2Me node dd016d64-f144-4085-a2f2-e67d7b3c3838

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_28174 (α β γ : ℝ) : α = π - (β + γ) → cos α = -cos (γ + β)   :=  by sorry

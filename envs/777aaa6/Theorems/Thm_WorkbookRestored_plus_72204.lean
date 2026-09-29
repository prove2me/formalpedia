-- Prove2me | Theorems.Thm_WorkbookRestored_plus_72204
-- name    : WorkbookRestored.plus_72204
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:57.201643+00:00
-- url     : https://prove2.me/theorems/85be4180-0409-4406-b4af-163cff3f598c
-- title:
--   Lean-Workbook Plus 72204: Trigonometric identity
-- statement:
--   For real $t$, $\cosh(3t)=\cosh t(4\cosh^2t-3)$. This is the first identity in the source.
--
--   Source: Lean-Workbook row `lean_workbook_plus_72204` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a0914547-1841-4195-b785-7a25f0b1472a); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_72204; immutable original Prove2Me node a0914547-1841-4195-b785-7a25f0b1472a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_72204 (t : ℝ) : Real.cosh (3 * t) = Real.cosh t * (4 * (Real.cosh t)^2 - 3)   :=  by sorry

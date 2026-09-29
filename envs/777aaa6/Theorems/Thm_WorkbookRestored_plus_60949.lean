-- Prove2me | Theorems.Thm_WorkbookRestored_plus_60949
-- name    : WorkbookRestored.plus_60949
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:40.303886+00:00
-- url     : https://prove2.me/theorems/dacc276f-4e80-4ac4-83f9-2769f064b795
-- title:
--   Lean-Workbook Plus 60949: Trigonometric inequality
-- statement:
--   for all real number of $x$ , then $\vert\sin{x}\vert + \vert\cos{x}\vert \geq 1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_60949` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/01a0a9c7-ff8b-4699-8a19-971a91c1dc38); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_60949; immutable original Prove2Me node 01a0a9c7-ff8b-4699-8a19-971a91c1dc38

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_60949 (x : ℝ) : abs (sin x) + abs (cos x) ≥ 1   :=  by sorry

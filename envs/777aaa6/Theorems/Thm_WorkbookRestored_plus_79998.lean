-- Prove2me | Theorems.Thm_WorkbookRestored_plus_79998
-- name    : WorkbookRestored.plus_79998
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:18:08.130073+00:00
-- url     : https://prove2.me/theorems/81f16317-94ac-4d6f-ae1b-907c12cf35bd
-- title:
--   Lean-Workbook Plus 79998: Trigonometric identity
-- statement:
--   For every real $x$, $\sin^4x=3/8-(4/8)\cos(2x)+(1/8)\cos(4x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_79998` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5924b96e-1f1f-4497-8d22-716390563b31); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_79998; immutable original Prove2Me node 5924b96e-1f1f-4497-8d22-716390563b31

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_79998 (x : ℝ) : (sin x)^4 = 3/8 - 4/8 * cos (2 * x) + 1/8 * cos (4 * x)   :=  by sorry

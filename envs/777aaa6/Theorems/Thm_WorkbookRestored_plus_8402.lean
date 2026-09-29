-- Prove2me | Theorems.Thm_WorkbookRestored_plus_8402
-- name    : WorkbookRestored.plus_8402
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:59.185576+00:00
-- url     : https://prove2.me/theorems/9ea941a3-7391-43af-8257-b586c4e7794c
-- title:
--   Lean-Workbook Plus 8402: Trigonometric inequality
-- statement:
--   For every real $x$, $-1\le\cos^6 x-\sin^4 x\le1$. This is the bounding component of the source question about extreme values; attainment is not asserted here.
--
--   Source: Lean-Workbook row `lean_workbook_plus_8402` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c6545858-932c-41d8-b3b9-419a86b2e771); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_8402; immutable original Prove2Me node c6545858-932c-41d8-b3b9-419a86b2e771

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_8402 (x : ℝ) : (-1 ≤ cos x ^ 6 - sin x ^ 4 ∧ cos x ^ 6 - sin x ^ 4 ≤ 1)   :=  by sorry

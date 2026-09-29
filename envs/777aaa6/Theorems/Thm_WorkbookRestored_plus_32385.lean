-- Prove2me | Theorems.Thm_WorkbookRestored_plus_32385
-- name    : WorkbookRestored.plus_32385
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:35.820979+00:00
-- url     : https://prove2.me/theorems/4816546d-62e2-45c6-bf65-54104b118645
-- title:
--   Lean-Workbook Plus 32385: Trigonometric identity
-- statement:
--   For every real $x$, $\sin^4x-\cos^4x=-\cos(2x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_32385` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/09c3ddc1-4351-4b14-8caa-3a71416e8195); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_32385; immutable original Prove2Me node 09c3ddc1-4351-4b14-8caa-3a71416e8195

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_32385 : ∀ x : ℝ, sin x ^ 4 - cos x ^ 4 = -cos (2 * x)   :=  by sorry

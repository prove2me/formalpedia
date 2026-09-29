-- Prove2me | Theorems.Thm_WorkbookRestored_plus_13487
-- name    : WorkbookRestored.plus_13487
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:31.400034+00:00
-- url     : https://prove2.me/theorems/97ccff9c-2f75-4558-adf0-ec6d909cfdd2
-- title:
--   Lean-Workbook Plus 13487: Trigonometric inequality
-- statement:
--   For every real $x$, $\tfrac14\le\cos^6 x+\sin^6 x\le1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_13487` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4c62a07d-1a9a-424f-8b41-f2f77582c4b2); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_13487; immutable original Prove2Me node 4c62a07d-1a9a-424f-8b41-f2f77582c4b2

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_13487 :
  ∀ x : ℝ, 1 / 4 ≤ cos x ^ 6 + sin x ^ 6 ∧ cos x ^ 6 + sin x ^ 6 ≤ 1   :=  by sorry

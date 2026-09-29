-- Prove2me | Theorems.Thm_WorkbookRestored_plus_15818
-- name    : WorkbookRestored.plus_15818
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:42.843595+00:00
-- url     : https://prove2.me/theorems/c14e0245-5a0b-4e62-b615-a2aacf602213
-- title:
--   Lean-Workbook Plus 15818: Trigonometric inequality
-- statement:
--   For every real $x$, $|\sin x+\cos x|+|\sin x-\cos x|\ge2\sin^2 x$. This formalizes the inequality in the source; it makes no assertion about equality cases.
--
--   Source: Lean-Workbook row `lean_workbook_plus_15818` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5c569a1b-c3ed-4672-8f6c-f5712ea987c0); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_15818; immutable original Prove2Me node 5c569a1b-c3ed-4672-8f6c-f5712ea987c0

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_15818 :
  ∀ x : ℝ,
    abs (sin x + cos x) + abs (sin x - cos x) ≥ 2 * (sin x)^2   :=  by sorry

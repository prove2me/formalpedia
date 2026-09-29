-- Prove2me | Theorems.Thm_WorkbookRestored_plus_46977
-- name    : WorkbookRestored.plus_46977
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:24.174067+00:00
-- url     : https://prove2.me/theorems/bcdd6d1b-4bc1-44ac-a5f5-99dc686a21cb
-- title:
--   Lean-Workbook Plus 46977: Trigonometric inequality
-- statement:
--   If $t=\sin x+\cos x$, then $\sin x\cos x=(t^2-1)/2$ and $|t|\le\sqrt2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_46977` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/be3ce3b4-1283-4dd7-95ac-c21067b7032e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_46977; immutable original Prove2Me node be3ce3b4-1283-4dd7-95ac-c21067b7032e

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_46977 (x : ℝ) (t : ℝ) (ht : t = sin x + cos x) : sin x * cos x = (t^2 - 1) / 2 ∧ |t| ≤ Real.sqrt 2   :=  by sorry

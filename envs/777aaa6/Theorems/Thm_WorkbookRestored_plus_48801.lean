-- Prove2me | Theorems.Thm_WorkbookRestored_plus_48801
-- name    : WorkbookRestored.plus_48801
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:50.469274+00:00
-- url     : https://prove2.me/theorems/c45f9ef3-8690-40fc-9bba-e52c0b0e2990
-- title:
--   Lean-Workbook Plus 48801: Logarithmic inequality
-- statement:
--   If real $n,h>0$ and $0.9^h n=0.5n$, then $h=\log(0.5)/\log(0.9)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_48801` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a7cd6071-5643-4298-b93f-3830ba876240); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_48801; immutable original Prove2Me node a7cd6071-5643-4298-b93f-3830ba876240

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_48801  (n : ℝ)
  (h : ℝ)
  (h₀ : 0 < n)
  (h₁ : 0 < h)
  (h₂ : (0.9^h) * n = 0.5 * n) :
  h = Real.log 0.5 / Real.log 0.9   :=  by sorry

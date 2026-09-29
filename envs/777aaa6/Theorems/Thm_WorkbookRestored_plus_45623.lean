-- Prove2me | Theorems.Thm_WorkbookRestored_plus_45623
-- name    : WorkbookRestored.plus_45623
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:09.978051+00:00
-- url     : https://prove2.me/theorems/edefd7b3-16c0-450b-b7b3-367392905980
-- title:
--   Lean-Workbook Plus 45623: Exponential inequality
-- statement:
--   For a positive natural number $n$ and $0\le x\le n$, $(1-x/n)^n\le e^{-x}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_45623` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4d93f5a9-54f5-44f2-a084-a990812f3296); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_45623; immutable original Prove2Me node 4d93f5a9-54f5-44f2-a084-a990812f3296

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Real

theorem WorkbookRestored.plus_45623 (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : 0 ≤ x ∧ x ≤ n) :
  (1 - x / n)^n ≤ exp (- x)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_57992
-- name    : WorkbookRestored.plus_57992
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:16.715511+00:00
-- url     : https://prove2.me/theorems/e71e1501-0ab5-41f9-905c-4e529eee76cf
-- title:
--   Lean-Workbook Plus 57992: Exponential inequality
-- statement:
--   For every natural number $n$ and real $0<p\le1$, $1-p^n<e^{-p^n}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_57992` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5ea9bc3b-a0e4-4d6f-9612-49d7d5b8e36e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_57992; immutable original Prove2Me node 5ea9bc3b-a0e4-4d6f-9612-49d7d5b8e36e

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_57992 (n : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
  (1 - p ^ n) < exp (-p ^ n)   :=  by sorry

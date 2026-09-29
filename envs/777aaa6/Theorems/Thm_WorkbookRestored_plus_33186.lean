-- Prove2me | Theorems.Thm_WorkbookRestored_plus_33186
-- name    : WorkbookRestored.plus_33186
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:41.737997+00:00
-- url     : https://prove2.me/theorems/4fec96e0-56f6-48a5-bf5e-8df4a6bb4cd3
-- title:
--   Lean-Workbook Plus 33186: Exponential inequality
-- statement:
--   For real $c,x$, $e^{cx}>0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_33186` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/81f2dab6-67e4-49c2-833c-4a50168df7fb); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_33186; immutable original Prove2Me node 81f2dab6-67e4-49c2-833c-4a50168df7fb

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_33186 (x : ℝ) (c : ℝ) : 0 < exp (c * x)   :=  by sorry

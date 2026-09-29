-- Prove2me | Theorems.Thm_WorkbookRestored_plus_54328
-- name    : WorkbookRestored.plus_54328
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:16:53.89015+00:00
-- url     : https://prove2.me/theorems/66833bad-58be-423d-8f45-adf0baf1dfaf
-- title:
--   Lean-Workbook Plus 54328: Exponential inequality
-- statement:
--   Given $ x \ge y$, prove that $ e^x - e^y \ge 0$
--
--   Source: Lean-Workbook row `lean_workbook_plus_54328` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/437d26c9-f495-4f44-aa19-af1b1e8eb03d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_54328; immutable original Prove2Me node 437d26c9-f495-4f44-aa19-af1b1e8eb03d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_54328 (x y : ℝ) (h : x ≥ y) : exp x - exp y ≥ 0   :=  by sorry

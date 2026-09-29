-- Prove2me | Theorems.Thm_WorkbookRestored_plus_26548
-- name    : WorkbookRestored.plus_26548
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:45.566757+00:00
-- url     : https://prove2.me/theorems/02d9b230-231e-44e0-9ba3-a4cd2ec68a1a
-- title:
--   Lean-Workbook Plus 26548: Logarithmic inequality
-- statement:
--   For every natural number $n\ge1$, $\log(n+1)<n$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_26548` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/69d57df0-8259-4ab5-9389-84a16bb4c572); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_26548; immutable original Prove2Me node 69d57df0-8259-4ab5-9389-84a16bb4c572

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_26548 (n : ℕ) (hn : 1 ≤ n) : Real.log (n + 1) < n   :=  by sorry

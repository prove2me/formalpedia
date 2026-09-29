-- Prove2me | Theorems.Thm_WorkbookRestored_plus_32948
-- name    : WorkbookRestored.plus_32948
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:38.814983+00:00
-- url     : https://prove2.me/theorems/e8656330-a18b-46f0-a74b-d688c0dcd672
-- title:
--   Lean-Workbook Plus 32948: Logarithmic inequality
-- statement:
--   For natural $n$ and real $D$, $|D-n\log2|<\sqrt n+1$ if and only if $n\log2-\sqrt n-1<D<n\log2+\sqrt n+1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_32948` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/dcd945c8-7248-4664-8cad-f8b09c2aba26); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_32948; immutable original Prove2Me node dcd945c8-7248-4664-8cad-f8b09c2aba26

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_32948 (n : ℕ) (D : ℝ) : |D - n * Real.log 2| < Real.sqrt n + 1 ↔ n * Real.log 2 - Real.sqrt n - 1 < D ∧ D < n * Real.log 2 + Real.sqrt n + 1   :=  by sorry

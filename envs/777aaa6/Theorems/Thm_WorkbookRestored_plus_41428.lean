-- Prove2me | Theorems.Thm_WorkbookRestored_plus_41428
-- name    : WorkbookRestored.plus_41428
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:31.786983+00:00
-- url     : https://prove2.me/theorems/d144dda2-ba22-4388-ba67-3652264790ec
-- title:
--   Lean-Workbook Plus 41428: Logarithmic inequality
-- statement:
--   For natural $n$ and $0\le x\le1$, $\log(1+nx/(n+1))\le\log(1+n/(n+1))$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_41428` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/bcc380cb-81d8-4e97-badf-cb0ec84bb71c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_41428; immutable original Prove2Me node bcc380cb-81d8-4e97-badf-cb0ec84bb71c

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_41428 (n : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  Real.log (1 + n * x / (n + 1)) ≤ Real.log (1 + n / (n + 1))   :=  by sorry

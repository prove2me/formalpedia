-- Prove2me | Theorems.Thm_WorkbookRestored_plus_80591
-- name    : WorkbookRestored.plus_80591
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:21:00.314573+00:00
-- url     : https://prove2.me/theorems/51cf6006-5100-4271-9262-411c6bdde393
-- title:
--   Lean-Workbook Plus 80591: Logarithmic inequality
-- statement:
--   For real $x>0$, if $\log x=\log6$, then $x=6$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_80591` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6a560d2f-a23d-4d8f-b794-d266aace1622); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_80591; immutable original Prove2Me node 6a560d2f-a23d-4d8f-b794-d266aace1622

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_80591  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : Real.log x = Real.log 6) :
  x = 6   :=  by sorry

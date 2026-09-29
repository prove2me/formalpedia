-- Prove2me | Theorems.Thm_WorkbookRestored_plus_5840
-- name    : WorkbookRestored.plus_5840
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:49.843168+00:00
-- url     : https://prove2.me/theorems/0a5baa20-b824-4a25-84d1-e0dee0ad9959
-- title:
--   Lean-Workbook Plus 5840: Logarithmic inequality
-- statement:
--   For every real $x<1$, $x+\log(1-x)\le0$. This statement formalizes the inequality component of the source; the source also asks to characterize equality.
--
--   Source: Lean-Workbook row `lean_workbook_plus_5840` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/e7354be3-3d9f-42e3-a521-3746aad45f60); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_5840; immutable original Prove2Me node e7354be3-3d9f-42e3-a521-3746aad45f60

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_5840 (x : ℝ) (hx : x < 1) : x + Real.log (1 - x) ≤ 0   :=  by sorry

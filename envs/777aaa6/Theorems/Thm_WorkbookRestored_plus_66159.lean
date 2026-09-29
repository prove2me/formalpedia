-- Prove2me | Theorems.Thm_WorkbookRestored_plus_66159
-- name    : WorkbookRestored.plus_66159
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:37.229599+00:00
-- url     : https://prove2.me/theorems/e866f3af-cc2b-4edd-b9f3-cc72f4abb537
-- title:
--   Lean-Workbook Plus 66159: A weighted cyclic real-power identity
-- statement:
--   For all real $a,b,c,r$, $(a^r+b^r-c^r)(a-b)^2+(b^r+c^r-a^r)(b-c)^2+(c^r+a^r-b^r)(c-a)^2=2\bigl(a^r(a-b)(a-c)+b^r(b-c)(b-a)+c^r(c-a)(c-b)\bigr)$. Powers use Lean's total real-power convention.
--
--   Source: Lean-Workbook row `lean_workbook_plus_66159` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/e9e07c4d-2ab7-4edb-8839-47c63d4ba0bd); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_66159; immutable original Prove2Me node e9e07c4d-2ab7-4edb-8839-47c63d4ba0bd

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem WorkbookRestored.plus_66159 (a b c r : ℝ) : (a^r + b^r - c^r)*(a - b)^2 + (b^r + c^r - a^r)*(b - c)^2 + (c^r + a^r - b^r)*(c - a)^2 = 2*(a^r*(a - b)*(a - c) + b^r*(b - c)*(b - a) + c^r*(c - a)*(c - b))   :=  by sorry

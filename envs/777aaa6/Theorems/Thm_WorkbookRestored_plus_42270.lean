-- Prove2me | Theorems.Thm_WorkbookRestored_plus_42270
-- name    : WorkbookRestored.plus_42270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:40.88948+00:00
-- url     : https://prove2.me/theorems/81e16e23-8535-4574-ad1f-06dcb4827dc3
-- title:
--   Lean-Workbook Plus 42270: Logarithmic inequality
-- statement:
--   For $a,b>0$, $2^{2a}a^ab^b<(a+b)^{a+b}$ if and only if $2a\log2+a\log a+b\log b-(a+b)\log(a+b)<0$, with real powers.
--
--   Source: Lean-Workbook row `lean_workbook_plus_42270` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/d4d77a13-f33a-49d6-8d06-85bc654d77c3); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_42270; immutable original Prove2Me node d4d77a13-f33a-49d6-8d06-85bc654d77c3

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_42270 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2:ℝ) ^ (2 * a) * a ^ a * b ^ b < (a + b) ^ (a + b) ↔ 2 * a * Real.log 2 + a * Real.log a + b * Real.log b - (a + b) * Real.log (a + b) < 0   :=  by sorry

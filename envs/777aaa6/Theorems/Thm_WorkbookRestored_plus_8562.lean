-- Prove2me | Theorems.Thm_WorkbookRestored_plus_8562
-- name    : WorkbookRestored.plus_8562
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:34.797984+00:00
-- url     : https://prove2.me/theorems/7a7b2047-43c6-4277-bab9-deeff3797a3c
-- title:
--   Adding exponents of a positive real base
-- statement:
--   For real $a,x,y$ with $a>0$, $$a^x a^y=a^{x+y}.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/46ff52ca-112b-4973-bfdb-2df4af04c685), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_8562` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_8562; original Prove2Me node 46ff52ca-112b-4973-bfdb-2df4af04c685; Apache-2.0

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_8562 (a x y : ℝ) (ha : 0 < a) : a^x * a^y = a^(x + y)   :=  by sorry

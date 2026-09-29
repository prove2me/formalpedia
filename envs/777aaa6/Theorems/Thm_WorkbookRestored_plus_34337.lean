-- Prove2me | Theorems.Thm_WorkbookRestored_plus_34337
-- name    : WorkbookRestored.plus_34337
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:56.257445+00:00
-- url     : https://prove2.me/theorems/81555d69-987a-4736-b88e-353f4476b3d9
-- title:
--   Lean-Workbook Plus 34337: Logarithmic inequality
-- statement:
--   For real $x\ge1$, $1-1/x\le\log x<1+x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34337` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5ab09bee-aa75-4193-aaa6-0a2f484fe9fe); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34337; immutable original Prove2Me node 5ab09bee-aa75-4193-aaa6-0a2f484fe9fe

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_34337 (x : ℝ) (hx : 1 ≤ x) : 1 - 1 / x ≤ Real.log x ∧ Real.log x < 1 + x   :=  by sorry

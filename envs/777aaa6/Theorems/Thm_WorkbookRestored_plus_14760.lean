-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14760
-- name    : WorkbookRestored.plus_14760
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:35.937887+00:00
-- url     : https://prove2.me/theorems/bb2b3f60-a71d-4030-a4f5-a5e3a2dbe03c
-- title:
--   Lean-Workbook Plus 14760: Logarithmic inequality
-- statement:
--   If $u>0$ and $u\ne1$, then $u-1-\log u>0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_14760` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/8cf63902-792e-4156-b0ee-c7719cb8a551); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14760; immutable original Prove2Me node 8cf63902-792e-4156-b0ee-c7719cb8a551

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_14760 (u : ℝ) (h : 0 < u) (h' : u ≠ 1) : u - 1 - Real.log u > 0   :=  by sorry

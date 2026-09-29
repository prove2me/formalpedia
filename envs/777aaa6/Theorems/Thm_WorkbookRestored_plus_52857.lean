-- Prove2me | Theorems.Thm_WorkbookRestored_plus_52857
-- name    : WorkbookRestored.plus_52857
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:46:12.409494+00:00
-- url     : https://prove2.me/theorems/74f62f53-a21f-4a52-9214-0fe7b91c34df
-- title:
--   Lean-Workbook Plus 52857: Strict monotonicity of real exponential powers
-- statement:
--   If $b>1$, then $b^x<b^y$ for all real $x<y$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_52857` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/abddddea-df9c-48e6-947b-d09c8600a63d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_52857; immutable original Prove2Me node abddddea-df9c-48e6-947b-d09c8600a63d

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem WorkbookRestored.plus_52857 (b : ℝ) (hb : 1 < b) : ∀ x y : ℝ, x < y → b^x < b^y   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_16252
-- name    : WorkbookRestored.plus_16252
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:50.273544+00:00
-- url     : https://prove2.me/theorems/ec0293d3-d8cf-446a-a7e0-d4e6fcc08d11
-- title:
--   Lean-Workbook Plus 16252: Logarithmic inequality
-- statement:
--   For every real $a>0$, $\cosh(\log a)=(a^2+1)/(2a)$. This formalizes part (a) of the source exercise; part (b) is a separate hyperbolic identity.
--
--   Source: Lean-Workbook row `lean_workbook_plus_16252` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c1b8f616-5daa-4947-81c5-d5d6387dc2fd); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_16252; immutable original Prove2Me node c1b8f616-5daa-4947-81c5-d5d6387dc2fd

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_16252 (a : ℝ) (ha : a > 0) : Real.cosh (Real.log a) = (a^2 + 1) / (2 * a)   :=  by sorry

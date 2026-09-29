-- Prove2me | Theorems.Thm_WorkbookRestored_plus_26180
-- name    : WorkbookRestored.plus_26180
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:43.643169+00:00
-- url     : https://prove2.me/theorems/02808629-ade8-43f7-8929-64f486d8ab32
-- title:
--   Lean-Workbook Plus 26180: Logarithmic inequality
-- statement:
--   For $x,a,b>0$, $\log_x a-\log_x b=\log_x(a/b)$. Here $\log_x t$ denotes Lean’s total ratio $\log t/\log x$, so the statement also includes $x=1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_26180` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/0121a0cc-64a0-40e9-8816-ed0b40fdc56e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_26180; immutable original Prove2Me node 0121a0cc-64a0-40e9-8816-ed0b40fdc56e

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_26180 (x a b : ℝ) (hx : x > 0) (hab : a > 0 ∧ b > 0) : Real.logb x a - Real.logb x b = Real.logb x (a / b)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_34341
-- name    : WorkbookRestored.plus_34341
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:06.571309+00:00
-- url     : https://prove2.me/theorems/e016182d-2cb1-451c-bbd3-326a9f661658
-- title:
--   Lean-Workbook Plus 34341: Logarithmic inequality
-- statement:
--   For positive real $a,b,c$, $\log_a b+\log_a c=\log_a(bc)$. The base logarithm is Lean’s total ratio $\log t/\log a$, including at $a=1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34341` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/17fbcfec-676d-481e-930b-2e4bf34d5ee0); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34341; immutable original Prove2Me node 17fbcfec-676d-481e-930b-2e4bf34d5ee0

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_34341 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → Real.logb a b + Real.logb a c = Real.logb a (b * c)   :=  by sorry

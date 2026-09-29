-- Prove2me | Theorems.Thm_WorkbookRestored_plus_21774
-- name    : WorkbookRestored.plus_21774
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:21.702182+00:00
-- url     : https://prove2.me/theorems/30ea7659-2c3a-4d33-92eb-6f077ac65ed5
-- title:
--   Lean-Workbook Plus 21774: Logarithmic inequality
-- statement:
--   If $a,b,c>0$ and $a,b,c\ne1$, then $(\log b/\log a)(\log c/\log b)=\log c/\log a$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_21774` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/affe610d-1fb8-4264-8924-9dc8f52fb962); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_21774; immutable original Prove2Me node affe610d-1fb8-4264-8924-9dc8f52fb962

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_21774 : ∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1) →  (Real.log b / Real.log a) * (Real.log c / Real.log b) = (Real.log c / Real.log a)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_56810
-- name    : WorkbookRestored.plus_56810
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:08.058655+00:00
-- url     : https://prove2.me/theorems/718345a1-c512-4e95-a061-ff8806141a79
-- title:
--   Lean-Workbook Plus 56810: Logarithmic inequality
-- statement:
--   For pairwise distinct positive real $a,b,c$, $\log_{cb^2}a+\log_{ac^2}b+\log_{ba^2}c=\frac{\log a}{2\log b+\log c}+\frac{\log b}{2\log c+\log a}+\frac{\log c}{2\log a+\log b}$. Base logarithms and division use Lean’s total convention.
--
--   Source: Lean-Workbook row `lean_workbook_plus_56810` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/05f6954c-e839-43f4-b045-f5d838cb50f1); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_56810; immutable original Prove2Me node 05f6954c-e839-43f4-b045-f5d838cb50f1

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_56810  (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : a ≠ c) :
  Real.logb (c * b^2) a + Real.logb (a * c^2) b + Real.logb (b * a^2) c =
    Real.log a / (2 * Real.log b + Real.log c) + Real.log b / (2 * Real.log c + Real.log a) +
      Real.log c / (2 * Real.log a + Real.log b)   :=  by sorry

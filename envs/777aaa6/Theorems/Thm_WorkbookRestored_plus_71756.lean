-- Prove2me | Theorems.Thm_WorkbookRestored_plus_71756
-- name    : WorkbookRestored.plus_71756
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:51.04942+00:00
-- url     : https://prove2.me/theorems/c7a41787-28b1-4989-ba12-01d2ea3a9dc9
-- title:
--   Lean-Workbook Plus 71756: Logarithmic inequality
-- statement:
--   For a positive natural number $n$, if $\log_{10}(12n)>\log_{10}75$, then $n>6$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_71756` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/2a63ced2-015a-4cd9-932d-8342aa8d90cc); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_71756; immutable original Prove2Me node 2a63ced2-015a-4cd9-932d-8342aa8d90cc

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_71756  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Real.logb 10 (12 * n) > Real.logb 10 75) :
  n > 6   :=  by sorry

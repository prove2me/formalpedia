-- Prove2me | Theorems.Thm_WorkbookRestored_plus_33584
-- name    : WorkbookRestored.plus_33584
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:48.128093+00:00
-- url     : https://prove2.me/theorems/c60124ed-15de-4a42-a477-b78570403e03
-- title:
--   Lean-Workbook Plus 33584: Exponential inequality
-- statement:
--   For every positive natural number $n$, $(\exp(2\pi i/n))^n-1=0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_33584` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a59c0200-4bc1-415b-95e0-437da02e407a); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_33584; immutable original Prove2Me node a59c0200-4bc1-415b-95e0-437da02e407a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_33584  (n : ℕ)
  (h₀ : 0 < n) :
  ((Complex.exp (2 * π * Complex.I / n))^n - 1) = 0   :=  by sorry

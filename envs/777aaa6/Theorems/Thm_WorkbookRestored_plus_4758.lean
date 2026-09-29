-- Prove2me | Theorems.Thm_WorkbookRestored_plus_4758
-- name    : WorkbookRestored.plus_4758
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:28.709759+00:00
-- url     : https://prove2.me/theorems/66393861-c0bc-4be6-8025-903ce5ebbe13
-- title:
--   Lean-Workbook Plus 4758: Exponential inequality
-- statement:
--   We have $\forall x\ge 1, e^{-x}\le 1\implies 1+e^{-x}\le 2\implies \frac{2}{x(1+e^{-x})}\ge \frac{1}{x}$
--
--   Source: Lean-Workbook row `lean_workbook_plus_4758` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/7a37f437-d0e9-415f-89c8-f9cab23f5e17); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_4758; immutable original Prove2Me node 7a37f437-d0e9-415f-89c8-f9cab23f5e17

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_4758 : ∀ x : ℝ, 1 ≤ x → 2 / (x * (1 + exp (-x))) ≥ 1 / x   :=  by sorry

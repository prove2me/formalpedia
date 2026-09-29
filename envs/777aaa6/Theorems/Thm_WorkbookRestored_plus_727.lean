-- Prove2me | Theorems.Thm_WorkbookRestored_plus_727
-- name    : WorkbookRestored.plus_727
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:16.343303+00:00
-- url     : https://prove2.me/theorems/618d6ac9-c651-4a00-b560-4ca3b813254f
-- title:
--   The principal root of one has unit norm
-- statement:
--   For every natural $n\ne0$, the principal complex power satisfies $|1^{1/n}|=1$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/f21e6850-1704-49b6-a569-e6ae650a1611), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_727` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_727; original Prove2Me node f21e6850-1704-49b6-a569-e6ae650a1611; Apache-2.0

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
open Complex

theorem WorkbookRestored.plus_727 (n : ℕ) (hn : n ≠ 0) : ‖(1 : ℂ) ^ (1 / n : ℂ)‖ = 1   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_5384
-- name    : WorkbookRestored.plus_5384
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:43.973123+00:00
-- url     : https://prove2.me/theorems/cae66d17-fc3d-417e-9a57-de7dc792edbd
-- title:
--   A real solution of a power equation
-- statement:
--   There exists a real number $x$ such that $x^2=2^x$. This node records existence, without classifying all solutions.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/ae6bea99-aadf-4cc3-99e9-5370860ed1d8), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_5384` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_5384; original Prove2Me node ae6bea99-aadf-4cc3-99e9-5370860ed1d8; Apache-2.0

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_5384 : ∃ x : ℝ, x^2 = 2^x   :=  by sorry

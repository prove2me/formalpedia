-- Prove2me | Theorems.Thm_WorkbookRestored_plus_3527
-- name    : WorkbookRestored.plus_3527
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:28.633431+00:00
-- url     : https://prove2.me/theorems/4e080c99-27eb-4e17-a38a-fd1195a63692
-- title:
--   Comparing two powers of a base between zero and one
-- statement:
--   If $0<x<1$, then $$x^{1/x}\le x^x.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/5662f2e0-c4af-44cd-9059-d84d6ebccdbb), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_3527` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_3527; original Prove2Me node 5662f2e0-c4af-44cd-9059-d84d6ebccdbb; Apache-2.0

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_3527 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  x^(1/x) ≤ x^x   :=  by sorry

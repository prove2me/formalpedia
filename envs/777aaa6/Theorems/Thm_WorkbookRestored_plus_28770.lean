-- Prove2me | Theorems.Thm_WorkbookRestored_plus_28770
-- name    : WorkbookRestored.plus_28770
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:23.201615+00:00
-- url     : https://prove2.me/theorems/387ce629-6d5f-4fd3-91fa-66581c27ce50
-- title:
--   A symmetric comparison of positive real powers
-- statement:
--   For $x\ge y>0$, $x^x y^y\ge x^y y^x$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/99f6d3cb-e242-478d-9b59-76fe95732fb7), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_28770` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_28770; original Prove2Me node 99f6d3cb-e242-478d-9b59-76fe95732fb7; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_28770 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≥ y) : x^x * y^y ≥ x^y * y^x   :=  by sorry

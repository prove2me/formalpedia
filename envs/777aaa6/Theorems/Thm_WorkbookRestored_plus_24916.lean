-- Prove2me | Theorems.Thm_WorkbookRestored_plus_24916
-- name    : WorkbookRestored.plus_24916
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:10.14013+00:00
-- url     : https://prove2.me/theorems/89a1b100-d251-44ba-83c0-109e7b42e7cf
-- title:
--   A nonnegative exponent of a base at least one
-- statement:
--   If $y\ge1$, then $y^{y-1}\ge1$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/0550411e-026a-44c5-8d78-45992624696f), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_24916` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_24916; original Prove2Me node 0550411e-026a-44c5-8d78-45992624696f; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_24916 (y : ℝ) (hy : 1 ≤ y) : y ^ (y - 1) ≥ 1   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_24509
-- name    : WorkbookRestored.plus_24509
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:08.435792+00:00
-- url     : https://prove2.me/theorems/91e72d17-ff48-4f96-a429-1783f9ff7656
-- title:
--   Comparing reciprocal and ordinary exponents above one
-- statement:
--   If $x>1$, then $x^{1/x}\le x^x$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/cc34ef08-2ef9-4859-b15c-992e2fe37c02), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_24509` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_24509; original Prove2Me node cc34ef08-2ef9-4859-b15c-992e2fe37c02; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_24509 (x : ℝ) (hx : 1 < x) : x^(1/x) ≤ x^x   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_45791
-- name    : WorkbookRestored.plus_45791
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:44.704615+00:00
-- url     : https://prove2.me/theorems/9628de10-0bba-4877-851b-5cb3fba27efd
-- title:
--   Dimension of a quotient space
-- statement:
--   For a real vector space $X$ and a subspace $Y$, $\dim Y+\dim(X/Y)=\dim X$. Dimensions are cardinal ranks, so the statement covers infinite-dimensional spaces as well.
--
--   Source: Lean-Workbook row `lean_workbook_plus_45791` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/8923a231-b5d6-458c-b554-cd99e810629c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_45791; immutable original Prove2Me node 8923a231-b5d6-458c-b554-cd99e810629c

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing

theorem WorkbookRestored.plus_45791 (X : Type*) [AddCommGroup X] [Module ℝ X]
    (Y : Submodule ℝ X) : Module.rank ℝ Y + Module.rank ℝ (X ⧸ Y) = Module.rank ℝ X   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_2271
-- name    : WorkbookRestored.plus_2271
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:51:05.976256+00:00
-- url     : https://prove2.me/theorems/eb7fca9e-b951-461b-a705-4bebce3b471e
-- title:
--   A cyclic determinant in two variables
-- statement:
--   For all complex numbers $x,y$, $$\det\begin{pmatrix}y&x&x+y\\x+y&y&x\\x&x+y&y\end{pmatrix}=2(x^3+y^3).$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/1cd95833-479e-4707-b429-79b1d0f6409c), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_2271` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_2271; original Prove2Me node 1cd95833-479e-4707-b429-79b1d0f6409c; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
open Matrix

theorem WorkbookRestored.plus_2271 (x y : ℂ) : Matrix.det (![![y, x, x+y],![x+y, y, x],![x, x+y, y]]) = 2 * (x^3 + y^3)   :=  by sorry

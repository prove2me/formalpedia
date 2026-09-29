-- Prove2me | Theorems.Thm_WorkbookRestored_plus_15411
-- name    : WorkbookRestored.plus_15411
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:20.438733+00:00
-- url     : https://prove2.me/theorems/0fd3b435-ebe2-4cf5-8341-e6faf5b75e96
-- title:
--   A determinant formed from pairwise sums of powers
-- statement:
--   For real $a,b,c$, $$\det\begin{pmatrix}a+b&b+c&c+a\\a^2+b^2&b^2+c^2&c^2+a^2\\a^3+b^3&b^3+c^3&c^3+a^3\end{pmatrix}=2abc(a-b)(b-c)(c-a).$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/38957f25-5b28-4e75-be65-d7459034c281), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_15411` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_15411; original Prove2Me node 38957f25-5b28-4e75-be65-d7459034c281; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open Matrix

theorem WorkbookRestored.plus_15411 (a b c : ℝ) : Matrix.det (![![a+b, b+c, c+a],![a^2+b^2, b^2+c^2, c^2+a^2],![a^3+b^3, b^3+c^3, c^3+a^3]]) = 2*a*b*c*(a-b)*(b-c)*(c-a)   :=  by sorry

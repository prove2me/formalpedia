-- Prove2me | Theorems.Thm_WorkbookRestored_plus_50816
-- name    : WorkbookRestored.plus_50816
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:52.445558+00:00
-- url     : https://prove2.me/theorems/c45f74dc-f5bb-44e2-8869-b33afac9527c
-- title:
--   A three by three circulant determinant
-- statement:
--   For real $a,b,c$, $\det\begin{pmatrix}a&b&c\\c&a&b\\b&c&a\end{pmatrix}=a^3+b^3+c^3-3abc$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_50816` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/51c4ccc2-929a-40e8-bae8-617d1a685430); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_50816; immutable original Prove2Me node 51c4ccc2-929a-40e8-bae8-617d1a685430

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem WorkbookRestored.plus_50816 (a b c : ℝ) :
  Matrix.det (![![a, b, c],![c, a, b],![b, c, a]]) = a^3 + b^3 + c^3 - 3*a*b*c   :=  by sorry

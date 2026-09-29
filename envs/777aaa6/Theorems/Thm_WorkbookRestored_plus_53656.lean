-- Prove2me | Theorems.Thm_WorkbookRestored_plus_53656
-- name    : WorkbookRestored.plus_53656
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:46:25.442704+00:00
-- url     : https://prove2.me/theorems/d958d7ea-80a6-4c25-8db4-8caacc475c8e
-- title:
--   Lean-Workbook Plus 53656: Symmetric three-by-three determinant
-- statement:
--   For real $a,b,c$, the determinant of $\begin{pmatrix}-2a&a+b&c+a\\a+b&-2b&b+c\\c+a&b+c&-2c\end{pmatrix}$ is $4(a+b)(b+c)(c+a)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_53656` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/155e92d9-bb21-43f0-a0cb-ef6db5110aa2); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_53656; immutable original Prove2Me node 155e92d9-bb21-43f0-a0cb-ef6db5110aa2

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem WorkbookRestored.plus_53656 (a b c : ℝ) : Matrix.det (![![-2*a, a+b, c+a],![a+b, -2*b, b+c],![c+a, b+c, -2*c]]) = 4*(a+b)*(b+c)*(c+a)   :=  by sorry

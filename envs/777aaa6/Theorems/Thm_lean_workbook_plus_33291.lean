-- Prove2me | Theorems.Thm_lean_workbook_plus_33291
-- name    : lean_workbook_plus_33291
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/e1fbf2ad-c71b-4989-85f7-88f56ee195e0
-- statement:
--   Expanding by minors on the third column gives us $1\cdot\text{det}\begin{pmatrix}\sin(x)&\cos(x)&0\\ -\cos(x)&\sin(x)&0\end{pmatrix} = \sin(x)^2+\cos(x)^2=\boxed{1}$ by the Pythagorean identity
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33291 :
  Matrix.det (![![sin x, cos x, 0],![-cos x, sin x, 0],![0, 0, 1]]) = 1   :=  by sorry
